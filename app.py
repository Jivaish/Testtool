from __future__ import annotations

import re
import time
import unicodedata
import xml.etree.ElementTree as ET
from collections import deque
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from io import BytesIO
from typing import Iterable
from urllib.parse import parse_qs, quote_plus, urldefrag, urljoin, urlparse, urlunparse

import pandas as pd
import requests
import streamlit as st
from bs4 import BeautifulSoup, Tag
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

try:
    import geonamescache
except Exception:  # pragma: no cover - handled in the UI
    geonamescache = None

try:
    import pycountry
except Exception:  # pragma: no cover - handled in the UI
    pycountry = None

try:
    from ddgs import DDGS
except Exception:  # pragma: no cover - handled in the UI
    DDGS = None

try:
    from pypdf import PdfReader
except Exception:  # pragma: no cover - PDF extraction is optional at runtime
    PdfReader = None


# ==================================================
# 1. Imports and constants
# ==================================================

APP_NAME = "Global Medical Faculty Contact Finder"
USER_AGENT = (
    "Mozilla/5.0 (compatible; GlobalMedicalFacultyContactFinder/1.0; "
    "+https://streamlit.io)"
)
HEADERS = {
    "User-Agent": USER_AGENT,
    "Accept-Language": "en-US,en;q=0.9",
}

DEFAULT_TIMEOUT = 16
MAX_RESPONSE_BYTES = 5 * 1024 * 1024
MAX_PDF_BYTES = 8 * 1024 * 1024

MEDIA_EXTENSIONS = (
    ".jpg", ".jpeg", ".png", ".gif", ".svg", ".webp", ".ico",
    ".zip", ".rar", ".7z", ".mp3", ".mp4", ".mov", ".avi", ".wmv",
    ".doc", ".docx", ".xls", ".xlsx", ".ppt", ".pptx",
)

BAD_SOURCE_HOST_MARKERS = (
    "linkedin.", "researchgate.", "facebook.", "twitter.", "x.com",
    "instagram.", "youtube.", "wikipedia.", "wikidata.", "yelp.",
    "healthgrades.", "doximity.", "ratemds.", "vitals.", "webmd.",
    "zoominfo.", "apollo.io", "rocketreach.", "hunter.io", "signalhire.",
    "crunchbase.", "usnews.", "niche.", "timeshighereducation.",
    "topuniversities.", "mastersportal.", "bachelorsportal.", "findaphd.",
    "indeed.", "glassdoor.", "salary.", "courseadvisor.", "collegefactual.",
    "collegesimply.", "petersons.", "study.com", "degreesearch.",
)

INSTITUTION_WORDS = (
    "university", "college", "school", "faculty", "medical", "medicine",
    "health", "hospital", "institute", "academy", "centre", "center",
    "polytechnic", "teaching hospital", "health sciences", "health-science",
)

STRONG_INSTITUTION_WORDS = (
    "university", "college", "school", "hospital", "health system",
    "medical center", "medical centre", "institute", "academy",
    "polytechnic", "teaching hospital", "cancer center", "cancer centre",
    "universidad", "universite", "universitat", "universita",
    "universidade", "universiteit", "universiti", "universitas",
    "uniwersytet", "universitet", "hochschule", "hogeschool", "ecole",
    "faculdade", "instituto", "institut", "akademi", "academia",
    "hopital", "krankenhaus", "klinikum", "szpital", "ospedale",
)

ACADEMIC_EVIDENCE_WORDS = (
    "academic", "academics", "degree", "degrees", "undergraduate",
    "graduate", "postgraduate", "students", "admissions", "education",
    "research", "residency", "fellowship", "faculty", "professor",
    "medical school", "school of medicine", "teaching hospital",
    "recherche", "forschung", "ricerca", "investigacion", "investigacao",
    "enseignement", "lehre", "docencia", "estudiantes", "studenten",
)

NON_INSTITUTION_PHRASES = (
    "iis windows server", "index of /", "page not found", "access denied",
    "contact us", "about the head", "continuing medical education",
    "physician jobs", "job opening", "job vacancies", "locum tenens",
    "mommy meltdown", "privacy policy", "terms of use", "search results",
    "find a doctor", "find a provider", "department of", "division of",
    "university system", "board of trustees",
    "list of universities", "universities list",
)

NON_INSTITUTION_PATH_WORDS = (
    "/jobs", "/careers", "/news", "/article", "/blog", "/events",
    "/course", "/cme", "/press-release", "/story",
)

DEPARTMENT_PAGE_WORDS = (
    "department", "school", "college", "faculty", "division", "centre",
    "center", "program", "programme", "specialty", "speciality",
    "academic unit", "institute", "clinic", "research",
)

FACULTY_PAGE_WORDS = (
    "faculty", "people", "staff", "directory", "our team", "academic staff",
    "teaching staff", "faculty profiles", "faculty directory", "researchers",
    "professors", "profiles", "profile", "team", "members", "directory",
)

COUNTRY_NAME_OVERRIDES = {
    "BO": "Bolivia",
    "BN": "Brunei",
    "CD": "Democratic Republic of the Congo",
    "CG": "Republic of the Congo",
    "CZ": "Czechia",
    "GB": "United Kingdom",
    "IR": "Iran",
    "KP": "North Korea",
    "KR": "South Korea",
    "LA": "Laos",
    "MD": "Moldova",
    "PS": "Palestine",
    "RU": "Russia",
    "SY": "Syria",
    "TZ": "Tanzania",
    "US": "United States",
    "VA": "Vatican City",
    "VE": "Venezuela",
    "VN": "Vietnam",
}


@st.cache_data(show_spinner=False)
def country_choices() -> list[tuple[str, str]]:
    if pycountry is None:
        return []
    countries = [
        (COUNTRY_NAME_OVERRIDES.get(item.alpha_2, item.name), item.alpha_2)
        for item in pycountry.countries
    ]
    return sorted(countries, key=lambda item: item[0].casefold())


@st.cache_data(show_spinner=False)
def location_choices(country_code: str) -> list[dict[str, str]]:
    if pycountry is None or geonamescache is None:
        return []

    subdivisions = list(pycountry.subdivisions.get(country_code=country_code) or [])
    subdivision_names = {
        item.code.split("-", 1)[-1]: item.name
        for item in subdivisions
    }
    choices: list[dict[str, str]] = [
        {"label": "All regions / nationwide", "value": "", "code": "", "kind": "Nationwide"}
    ]
    seen: set[tuple[str, str, str]] = set()

    for item in subdivisions:
        kind = clean_text(getattr(item, "type", "Region")) or "Region"
        key = (kind.casefold(), item.name.casefold(), "")
        if key in seen:
            continue
        seen.add(key)
        choices.append({
            "label": f"{item.name} - {kind}",
            "value": item.name,
            "code": item.code,
            "kind": kind,
        })

    cache = geonamescache.GeonamesCache(min_city_population=500)
    for city in cache.get_cities().values():
        if city.get("countrycode") != country_code:
            continue
        name = clean_text(city.get("name"))
        if not name:
            continue
        parent = subdivision_names.get(clean_text(city.get("admin1code")), "")
        key = ("city", name.casefold(), parent.casefold())
        if key in seen:
            continue
        seen.add(key)
        label = f"{name} - City"
        if parent and parent.casefold() != name.casefold():
            label += f", {parent}"
        choices.append({
            "label": label,
            "value": name,
            "code": clean_text(city.get("admin1code")),
            "kind": "City",
        })

    return choices[:1] + sorted(choices[1:], key=lambda item: item["label"].casefold())


# ==================================================
# 2. Department keyword registry
# ==================================================

SPECIALTIES = [
    "Obstetrics and Gynecology",
    "Pediatrics",
    "Nursing",
    "Physiotherapy",
    "Cardiology",
    "Oncology",
    "Neurology",
    "Psychiatry",
    "Public Health",
    "Pharmacy",
    "Dentistry",
    "Radiology",
    "Orthopedics",
    "Emergency Medicine",
    "Custom Department",
]

SPECIALTY_TERMS: dict[str, list[str]] = {
    "Obstetrics and Gynecology": [
        "obstetrics", "gynecology", "gynaecology", "obgyn", "ob-gyn",
        "ob/gyn", "women's health", "womens health",
        "maternal-fetal medicine", "maternal fetal medicine",
        "reproductive endocrinology", "reproductive medicine",
        "gynecologic oncology", "gynaecologic oncology", "urogynecology",
        "urogynaecology", "family planning", "maternal medicine",
    ],
    "Pediatrics": [
        "pediatrics", "paediatrics", "child health", "neonatology",
        "adolescent medicine", "pediatric surgery", "paediatric surgery",
        "newborn medicine", "children's health", "child development",
    ],
    "Nursing": [
        "nursing", "school of nursing", "college of nursing",
        "faculty of nursing", "nursing science", "nursing faculty",
        "adult health nursing", "community health nursing",
        "pediatric nursing", "paediatric nursing", "mental health nursing",
        "public health nursing", "clinical nursing",
    ],
    "Physiotherapy": [
        "physiotherapy", "physical therapy", "rehabilitation",
        "physical rehabilitation", "kinesiology", "exercise science",
        "sports science", "sports medicine", "biomechanics",
        "human movement", "motor control", "movement science",
        "strength and conditioning", "clinical exercise physiology",
        "exercise physiology", "sports physiotherapy",
        "musculoskeletal rehabilitation",
    ],
    "Cardiology": [
        "cardiology", "cardiovascular medicine", "cardiovascular sciences",
        "cardiac sciences", "heart institute", "heart centre", "heart center",
    ],
    "Oncology": [
        "oncology", "medical oncology", "radiation oncology", "cancer centre",
        "cancer center", "cancer institute", "hematology oncology",
    ],
    "Neurology": [
        "neurology", "neuroscience", "clinical neuroscience",
        "neurological sciences", "brain sciences",
    ],
    "Psychiatry": [
        "psychiatry", "mental health", "behavioral health",
        "behavioural health", "psychological medicine",
    ],
    "Public Health": [
        "public health", "population health", "epidemiology",
        "global health", "community health", "health policy",
    ],
    "Pharmacy": [
        "pharmacy", "pharmaceutical sciences", "clinical pharmacy",
        "pharmacology", "school of pharmacy", "college of pharmacy",
    ],
    "Dentistry": [
        "dentistry", "dental medicine", "oral health", "dental school",
        "oral and maxillofacial",
    ],
    "Radiology": [
        "radiology", "medical imaging", "diagnostic imaging",
        "radiological sciences", "imaging sciences",
    ],
    "Orthopedics": [
        "orthopedics", "orthopaedics", "orthopedic surgery",
        "orthopaedic surgery", "musculoskeletal medicine",
    ],
    "Emergency Medicine": [
        "emergency medicine", "emergency care", "acute care",
        "emergency medical services",
    ],
    "Custom Department": [],
}


def clean_term(value: str) -> str:
    return re.sub(r"\s+", " ", (value or "").strip().lower())


def resolve_terms(specialty: str, custom_keywords: str = "") -> list[str]:
    terms = list(SPECIALTY_TERMS.get(specialty, []))
    terms.extend(clean_term(item) for item in (custom_keywords or "").split(","))
    seen: set[str] = set()
    ordered: list[str] = []
    for term in terms:
        if term and term not in seen:
            seen.add(term)
            ordered.append(term)
    return ordered


# ==================================================
# 3. Data classes
# ==================================================

@dataclass
class Institution:
    name: str
    official_url: str
    host: str
    source_query: str
    score: int


@dataclass
class PageCandidate:
    url: str
    title: str
    matched_terms: list[str]
    source: str
    score: int


@dataclass
class FacultyEntry:
    name: str
    normalized_name: str
    title: str
    source_url: str
    evidence: str = ""
    profile_url: str | None = None


@dataclass
class Contact:
    name: str
    email: str
    institution: str
    source_url: str
    method: str
    strength: int = 5

    def final_row(self) -> dict[str, str]:
        return {"Name": self.name, "Email": self.email}


@dataclass
class Rejection:
    name: str
    reason: str
    source_url: str = ""
    detail: str = ""


@dataclass
class InstitutionReport:
    institution: str
    status: str
    official_url: str
    department_pages: int = 0
    faculty_roster_entries: int = 0
    pages_checked: int = 0
    profiles_checked: int = 0
    contacts_found: int = 0
    notes: list[str] = field(default_factory=list)
    blocked_or_unreadable: list[str] = field(default_factory=list)
    rejections: list[Rejection] = field(default_factory=list)

    def as_row(self) -> dict[str, object]:
        return {
            "Institution": self.institution,
            "Status": self.status,
            "Official URL": self.official_url,
            "Department Pages": self.department_pages,
            "Roster Entries": self.faculty_roster_entries,
            "Pages Checked": self.pages_checked,
            "Profiles Checked": self.profiles_checked,
            "Contacts": self.contacts_found,
            "Notes": "; ".join(self.notes[:6]),
        }


# ==================================================
# 4. URL and domain helpers
# ==================================================

def clean_text(value: object) -> str:
    return re.sub(r"\s+", " ", str(value or "").replace("\xa0", " ")).strip()


def fold_text(value: object) -> str:
    normalized = unicodedata.normalize("NFKD", clean_text(value))
    return normalized.encode("ascii", "ignore").decode("ascii").casefold()


def normalize_url(url: str) -> str | None:
    if not url:
        return None
    url, _ = urldefrag(url.strip())
    parsed = urlparse(url)
    if not parsed.scheme:
        url = "https://" + url
        parsed = urlparse(url)
    if parsed.scheme not in {"http", "https"} or not parsed.netloc:
        return None
    if parsed.path.lower().endswith(MEDIA_EXTENSIONS):
        return None
    return url.rstrip("/")


def url_root(url: str) -> str | None:
    parsed = urlparse(url)
    if not parsed.scheme or not parsed.netloc:
        return None
    return f"{parsed.scheme}://{parsed.netloc}"


def host_of(url: str) -> str:
    return (urlparse(url).hostname or "").lower().removeprefix("www.")


def organization_root(host: str) -> str:
    host = (host or "").lower().strip(".").removeprefix("www.")
    parts = [part for part in host.split(".") if part]
    if len(parts) <= 2:
        return host
    second_level_suffixes = {
        "ac", "edu", "co", "com", "org", "gov", "net", "nhs", "sch",
    }
    if len(parts[-1]) == 2 and parts[-2] in second_level_suffixes:
        return ".".join(parts[-3:])
    return ".".join(parts[-2:])


def related_official_domain(url_or_host: str, official_host: str) -> bool:
    host = host_of(url_or_host) if "://" in url_or_host else url_or_host.lower()
    official_host = official_host.lower().removeprefix("www.")
    if not host or not official_host:
        return False
    if host == official_host or host.endswith("." + official_host):
        return True
    return organization_root(host) == organization_root(official_host)


def is_bad_external_source(url: str) -> bool:
    host = host_of(url)
    return any(marker in host for marker in BAD_SOURCE_HOST_MARKERS)


def make_session() -> requests.Session:
    session = requests.Session()
    retry = Retry(
        total=2,
        connect=2,
        read=2,
        backoff_factor=0.35,
        status_forcelist=(429, 500, 502, 503, 504),
        allowed_methods=("GET", "HEAD"),
    )
    session.mount("http://", HTTPAdapter(max_retries=retry))
    session.mount("https://", HTTPAdapter(max_retries=retry))
    return session


def fetch_response(
    session: requests.Session,
    url: str,
    timeout: int = DEFAULT_TIMEOUT,
    max_bytes: int = MAX_RESPONSE_BYTES,
) -> tuple[requests.Response | None, str | None, str | None]:
    try:
        response = session.get(
            url,
            headers=HEADERS,
            timeout=timeout,
            allow_redirects=True,
            stream=True,
        )
        if response.status_code in {401, 403, 429}:
            return None, normalize_url(response.url) or url, f"Blocked or rate limited ({response.status_code})"
        response.raise_for_status()

        content_length = response.headers.get("Content-Length")
        if content_length and int(content_length) > max_bytes:
            response.close()
            return None, normalize_url(response.url) or url, "Response too large"

        chunks: list[bytes] = []
        total = 0
        for chunk in response.iter_content(chunk_size=65536):
            total += len(chunk)
            if total > max_bytes:
                response.close()
                return None, normalize_url(response.url) or url, "Response too large"
            chunks.append(chunk)
        response._content = b"".join(chunks)
        return response, normalize_url(response.url), None
    except requests.RequestException as exc:
        return None, None, exc.__class__.__name__


def fetch_html(session: requests.Session, url: str) -> tuple[str | None, str | None, str | None]:
    response, final_url, error = fetch_response(session, url)
    if not response or not final_url:
        return None, final_url, error
    content_type = response.headers.get("Content-Type", "").lower()
    if "html" not in content_type and not response.text.lstrip().startswith("<"):
        return None, final_url, "Not HTML"
    return response.text, final_url, None


def is_pdf_url(url: str) -> bool:
    return urlparse(url).path.lower().endswith(".pdf")


def fetch_pdf_text(session: requests.Session, url: str) -> tuple[str | None, str | None]:
    if PdfReader is None:
        return None, "pypdf is not available"
    response, final_url, error = fetch_response(session, url, max_bytes=MAX_PDF_BYTES)
    if not response:
        return None, error or "PDF unavailable"
    content_type = response.headers.get("Content-Type", "").lower()
    if "pdf" not in content_type and not is_pdf_url(final_url or url):
        return None, "Not PDF"
    try:
        reader = PdfReader(BytesIO(response.content))
        page_text = []
        for page in reader.pages:
            page_text.append(page.extract_text() or "")
        return clean_text("\n".join(page_text)), None
    except Exception as exc:
        return None, exc.__class__.__name__


def fetch_robots_txt(session: requests.Session, official_url: str) -> str | None:
    root = url_root(official_url)
    if not root:
        return None
    try:
        response = session.get(f"{root}/robots.txt", headers=HEADERS, timeout=8)
        if response.status_code == 200:
            return response.text
    except requests.RequestException:
        return None
    return None


def parse_disallowed_paths(robots_text: str, user_agent: str = "*") -> list[str]:
    disallowed: list[str] = []
    current_agents: list[str] = []
    applies = False
    for raw_line in (robots_text or "").splitlines():
        line = raw_line.split("#", 1)[0].strip()
        if not line or ":" not in line:
            continue
        key, _, value = line.partition(":")
        key = key.strip().lower()
        value = value.strip()
        if key == "user-agent":
            if current_agents and applies:
                current_agents = []
            current_agents.append(value.lower())
            applies = "*" in current_agents or user_agent.lower() in current_agents
        elif key == "disallow" and applies and value:
            disallowed.append(value)
    return disallowed


def path_allowed(url: str, disallowed_paths: list[str]) -> bool:
    path = urlparse(url).path or "/"
    return not any(path.startswith(rule) for rule in disallowed_paths if rule)


def slugify(value: str) -> str:
    return re.sub(r"[^a-z0-9]+", "-", value.lower()).strip("-")


# ==================================================
# 5. Search helpers
# ==================================================

COUNTRY_DOMAIN_HINTS = {
    "united states": [".edu", ".org"],
    "usa": [".edu", ".org"],
    "united kingdom": [".ac.uk", ".nhs.uk"],
    "uk": [".ac.uk", ".nhs.uk"],
    "england": [".ac.uk", ".nhs.uk"],
    "australia": [".edu.au", ".org.au"],
    "india": [".edu.in", ".ac.in", ".org"],
    "turkey": [".edu.tr", ".org.tr"],
    "germany": [".de"],
    "canada": [".ca"],
    "ireland": [".ie"],
    "new zealand": [".ac.nz"],
}


def ddg_search(query: str) -> list[dict[str, str]]:
    if DDGS is None:
        return []
    results: list[dict[str, str]] = []
    try:
        with DDGS() as ddgs:
            for item in ddgs.text(query, max_results=None):
                href = item.get("href") or item.get("url") or ""
                title = item.get("title") or ""
                body = item.get("body") or item.get("snippet") or ""
                if href:
                    results.append({"url": href, "title": title, "body": body, "query": query})
    except Exception:
        return []
    return results


def domain_hints_for_country(country: str, country_code: str = "") -> list[str]:
    key = clean_term(country)
    hints = list(COUNTRY_DOMAIN_HINTS.get(key, []))
    code = country_code.casefold()
    if code and code != "us":
        hints.extend([f".{code}", f".ac.{code}", f".edu.{code}"])
    seen: set[str] = set()
    return [hint for hint in hints if not (hint in seen or seen.add(hint))]


def build_institution_queries(
    country: str,
    country_code: str,
    region: str,
    specialty: str,
    terms: list[str],
) -> list[str]:
    location = clean_text(" ".join(part for part in [region, country] if part)).strip()
    primary_term = terms[0] if terms else specialty
    queries = [
        f'"{location}" university official website -jobs -news',
        f'"{location}" medical school official website -jobs -news',
        f'"{location}" health sciences university official website',
        f'"{location}" academic teaching hospital official website',
        f'"{location}" "{primary_term}" faculty university official',
        f'"{location}" "{primary_term}" medical school faculty',
        f'"{location}" "{primary_term}" college faculty directory',
        f'"{location}" "{specialty}" academic department faculty',
    ]
    for hint in domain_hints_for_country(country, country_code):
        queries.extend([
            f'site:{hint} "{region or country}" "{primary_term}" faculty',
            f'site:{hint} "{region or country}" "{specialty}" department',
        ])
    seen: set[str] = set()
    return [q for q in queries if not (q in seen or seen.add(q))]


def is_academic_domain(host: str) -> bool:
    return bool(
        host.endswith(".edu")
        or re.search(r"\.(?:ac|edu)\.[a-z]{2}$", host)
        or host.endswith(".nhs.uk")
    )


def score_institution_result(
    url: str,
    title: str,
    body: str,
    country: str,
    country_code: str,
    terms: list[str],
) -> int:
    host = host_of(url)
    if not host or is_bad_external_source(url):
        return -100
    combined = fold_text(f"{url} {title} {body}")
    academic_host = is_academic_domain(host)
    score = 0
    if academic_host:
        score += 45
    if any(word in combined for word in STRONG_INSTITUTION_WORDS):
        score += 30
    elif any(word in combined for word in INSTITUTION_WORDS):
        score += 10
    if any(fold_text(term) in combined for term in terms):
        score += 4
    for hint in domain_hints_for_country(country, country_code):
        if host.endswith(hint.lstrip(".")) or hint in host:
            score += 12
    if any(word in host for word in ("university", "college", "school", "hospital", "health", "med")):
        score += 12
    if "official" in combined:
        score += 4
    if not academic_host and any(path_word in urlparse(url).path.casefold() for path_word in NON_INSTITUTION_PATH_WORDS):
        score -= 35
    if not academic_host and any(phrase in combined for phrase in NON_INSTITUTION_PHRASES):
        score -= 60
    if any(bad in combined for bad in ("ranking", "wikipedia", "linkedin", "facebook", "directory listing")):
        score -= 50
    return score


def clean_institution_name_candidate(value: str) -> str:
    value = re.sub(r"\b(official site|official website|home|homepage|faculty directory)\b", "", value, flags=re.I)
    value = re.sub(r"\s+(?:official\s+)?logo\s*$", "", value, flags=re.I)
    return clean_text(value.strip(" -|:"))


def valid_institution_name(value: str, host: str) -> bool:
    name = clean_institution_name_candidate(value)
    folded = fold_text(name)
    words = name.split()
    if not 2 <= len(name) <= 100 or len(words) > 15:
        return False
    if any(phrase in folded for phrase in NON_INSTITUTION_PHRASES):
        return False
    if "top ranked university" in folded:
        return False
    if re.match(r"^(about|contact|welcome|department|division|faculty|school news)\b", folded):
        return False
    if any(mark in folded for mark in ("http://", "https://", "www.")):
        return False
    has_identity = any(word in folded for word in STRONG_INSTITUTION_WORDS)
    has_medical_brand = any(word in folded for word in ("medicine", "health", "clinic", "cancer center", "cancer centre"))
    is_acronym = name.replace("&", "").replace(" ", "").isalnum() and name.upper() == name and len(name) <= 16
    return has_identity or has_medical_brand or (is_acronym and is_academic_domain(host))


def extract_institution_name(soup: BeautifulSoup, search_title: str, host: str) -> str | None:
    candidates: list[tuple[int, str]] = []
    for attribute, weight in (("og:site_name", 120), ("application-name", 115)):
        meta = soup.find("meta", attrs={"property": attribute}) or soup.find("meta", attrs={"name": attribute})
        if meta and meta.get("content"):
            meta_name = clean_text(meta.get("content"))
            candidates.append((weight, meta_name))
            for part in re.split(r"\s+(?:\||-|\u2013|\u2014|:)\s+", meta_name):
                candidates.append((weight + 8, part))

    homepage_title = clean_text(soup.title.get_text(" ", strip=True) if soup.title else "")
    for source_title, weight in ((homepage_title, 100), (search_title, 20)):
        if not source_title:
            continue
        candidates.append((weight, source_title))
        for part in re.split(r"\s+(?:\||-|\u2013|\u2014|:)\s+", source_title):
            candidates.append((weight + 8, part))

    for anchor in soup.find_all("a", href=True):
        href = normalize_url(urljoin(f"https://{host}", anchor.get("href", "")))
        if not href or not related_official_domain(href, host) or urlparse(href).path not in {"", "/"}:
            continue
        text = clean_text(anchor.get_text(" ", strip=True))
        if text:
            candidates.append((90, text))
        for image in anchor.find_all("img", alt=True):
            candidates.append((95, clean_text(image.get("alt"))))

    scored: list[tuple[int, str]] = []
    for source_weight, raw_name in candidates:
        name = clean_institution_name_candidate(raw_name)
        if not valid_institution_name(name, host):
            continue
        folded = fold_text(name)
        score = source_weight
        score += 45 * any(word in folded for word in ("university", "college", "hospital"))
        score += 25 * any(
            word in folded
            for word in ("school", "institute", "medical center", "medical centre", "cancer center", "cancer centre")
        )
        if re.search(r"\s(?:\||-|\u2013|\u2014|:)\s", name):
            score -= 35
        score -= max(0, len(name.split()) - 10) * 3
        scored.append((score, name))

    if not scored:
        return None
    return sorted(scored, key=lambda item: (-item[0], len(item[1]), item[1].casefold()))[0][1]


def homepage_has_academic_identity(name: str, soup: BeautifulSoup, host: str) -> bool:
    title = clean_text(soup.title.get_text(" ", strip=True) if soup.title else "")
    if any(phrase in fold_text(title) for phrase in NON_INSTITUTION_PHRASES):
        return False
    text = fold_text(soup.get_text(" ", strip=True))
    brand_text = fold_text(f"{name} {title}")
    if ("system" in host or "university system" in text) and "health system" not in brand_text:
        return False
    evidence_count = sum(word in text for word in ACADEMIC_EVIDENCE_WORDS)
    strong_name = any(word in fold_text(name) for word in STRONG_INSTITUTION_WORDS)
    if is_academic_domain(host):
        return strong_name or evidence_count >= 2
    return strong_name and evidence_count >= 2


def homepage_matches_location(
    name: str,
    soup: BeautifulSoup,
    host: str,
    country: str,
    country_code: str,
    region: str,
    region_code: str,
    region_kind: str,
) -> bool:
    text = clean_text(soup.get_text(" ", strip=True))
    corpus = f"{name} {text}"
    folded = fold_text(corpus)
    if region:
        if fold_text(region) in folded:
            return True
        if region_kind == "City":
            return False
        abbreviation = region_code.rsplit("-", 1)[-1].upper()
        if len(abbreviation) in {2, 3}:
            return bool(re.search(rf"(?:,\s*|\b){re.escape(abbreviation)}\s+\d{{4,6}}\b", corpus))
        return False

    code = country_code.casefold()
    if fold_text(country) in folded:
        return True
    if code and host.endswith(f".{code}"):
        return True
    if code == "us" and (host.endswith(".edu") or re.search(r"\b[A-Z]{2}\s+\d{5}(?:-\d{4})?\b", corpus)):
        return True
    if code == "gb" and host.endswith(".uk"):
        return True
    return False


def canonical_institution_url(raw_url: str) -> str | None:
    normalized = normalize_url(raw_url)
    if not normalized:
        return None
    parsed = urlparse(normalized)
    if is_bad_external_source(normalized):
        return None
    root_host = organization_root(parsed.hostname or "")
    if not root_host:
        return None
    return f"{parsed.scheme}://{root_host}"


# ==================================================
# 6. Institution discovery
# ==================================================

@st.cache_data(show_spinner=False, ttl=60 * 60 * 12)
def discover_institutions(
    country: str,
    country_code: str,
    region: str,
    region_code: str,
    region_kind: str,
    specialty: str,
    custom_keywords: str,
) -> tuple[list[Institution], list[str]]:
    terms = resolve_terms(specialty, custom_keywords)
    queries = build_institution_queries(country, country_code, region, specialty, terms)
    institutions_by_root: dict[str, Institution] = {}
    candidates_by_root: dict[str, tuple[int, str, dict[str, str]]] = {}
    log: list[str] = []

    for query in queries:
        search_results = ddg_search(query)
        log.append(f"{query}: {len(search_results)} result(s)")
        for result in search_results:
            candidate_url = canonical_institution_url(result["url"])
            if not candidate_url:
                continue
            host = host_of(candidate_url)
            root = organization_root(host)
            score = score_institution_result(
                result["url"],
                result["title"],
                result["body"],
                country,
                country_code,
                terms,
            )
            if score < 35:
                continue
            result_text = fold_text(f"{result['url']} {result['title']} {result['body']}")
            has_specialty_evidence = any(fold_text(term) in result_text for term in terms)
            enriched_result = {
                **result,
                "candidate_url": candidate_url,
                "specialty_evidence": "1" if has_specialty_evidence else "0",
            }
            existing_candidate = candidates_by_root.get(root)
            existing_has_evidence = bool(existing_candidate and existing_candidate[2]["specialty_evidence"] == "1")
            if (
                not existing_candidate
                or (has_specialty_evidence and not existing_has_evidence)
                or (has_specialty_evidence == existing_has_evidence and score > existing_candidate[0])
            ):
                candidates_by_root[root] = (score, query, enriched_result)

    def verify_candidate(payload: tuple[int, str, dict[str, str]]) -> tuple[str, Institution | None, str]:
        score, query, result = payload
        candidate_url = result["candidate_url"]
        session = make_session()
        html, final_url, error = fetch_html(session, candidate_url)
        root = organization_root(host_of(candidate_url))
        if not html or not final_url:
            message = f"Rejected {candidate_url}: homepage could not be verified ({error or 'unavailable'})"
            return root, None, message

        candidate_url = canonical_institution_url(final_url) or candidate_url
        host = host_of(candidate_url)
        root = organization_root(host)
        soup = BeautifulSoup(html, "html.parser")
        name = extract_institution_name(soup, result["title"], host)
        if not name:
            return root, None, f"Rejected {candidate_url}: no valid institution brand found on homepage"
        if not homepage_has_academic_identity(name, soup, host):
            message = f"Rejected {candidate_url}: homepage did not verify an academic or teaching institution"
            return root, None, message
        if not homepage_matches_location(name, soup, host, country, country_code, region, region_code, region_kind):
            location_label = region or country
            message = f"Rejected {candidate_url}: official homepage did not verify location {location_label}"
            return root, None, message

        page_title = clean_text(soup.title.get_text(" ", strip=True) if soup.title else "")
        score += score_institution_result(
            candidate_url,
            page_title,
            soup.get_text(" ", strip=True)[:4000],
            country,
            country_code,
            terms,
        ) // 3
        item = Institution(
            name=name,
            official_url=candidate_url,
            host=host,
            source_query=query,
            score=score,
        )
        return root, item, f"Accepted {name}: {candidate_url}"

    eligible_candidates: list[tuple[int, str, dict[str, str]]] = []
    for payload in candidates_by_root.values():
        if payload[2]["specialty_evidence"] == "1":
            eligible_candidates.append(payload)
        else:
            log.append(
                f"Rejected {payload[2]['candidate_url']}: no official search evidence for {specialty}"
            )

    with ThreadPoolExecutor(max_workers=8) as executor:
        verified = executor.map(verify_candidate, eligible_candidates)
        for root, item, message in verified:
            log.append(message)
            if item is None:
                continue
            existing = institutions_by_root.get(root)
            if not existing or item.score > existing.score:
                institutions_by_root[root] = item

    institutions = sorted(
        institutions_by_root.values(),
        key=lambda item: (-item.score, item.name.lower()),
    )
    return institutions, log


# ==================================================
# 7. Department discovery
# ==================================================

def text_matches_terms(text: str, terms: Iterable[str]) -> list[str]:
    lowered = clean_text(text).lower()
    return [term for term in terms if term and term in lowered]


def relevance_score(url: str, title: str, page_text: str, terms: list[str]) -> int:
    combined = f"{url} {title} {page_text[:2500]}".lower()
    score = 0
    score += 30 * len(text_matches_terms(combined, terms))
    score += 12 * sum(word in combined for word in DEPARTMENT_PAGE_WORDS)
    score += 14 * sum(word in combined for word in FACULTY_PAGE_WORDS)
    if any(word in combined for word in ("faculty", "people", "directory", "profile")):
        score += 18
    return score


def extract_sitemap_urls(xml_text: str) -> list[str]:
    try:
        root = ET.fromstring(xml_text)
    except ET.ParseError:
        return []
    urls: list[str] = []
    for element in root.iter():
        if element.tag.lower().endswith("loc") and element.text:
            normalized = normalize_url(element.text.strip())
            if normalized:
                urls.append(normalized)
    return urls


def discover_sitemaps(session: requests.Session, official_url: str) -> list[str]:
    root = url_root(official_url)
    if not root:
        return []
    sitemap_urls = {f"{root}/sitemap.xml", f"{root}/sitemap_index.xml"}
    robots_text = fetch_robots_txt(session, official_url)
    if robots_text:
        for line in robots_text.splitlines():
            if line.lower().startswith("sitemap:"):
                value = normalize_url(line.split(":", 1)[1].strip())
                if value:
                    sitemap_urls.add(value)
    return sorted(sitemap_urls)


def common_department_paths(official_url: str, terms: list[str]) -> list[str]:
    root = url_root(official_url)
    if not root:
        return []
    slugs: set[str] = set()
    for term in terms:
        slug = slugify(term)
        compact = re.sub(r"[^a-z0-9]+", "", term.lower())
        if slug:
            slugs.add(slug)
        if compact:
            slugs.add(compact)
    prefixes = (
        "", "department", "departments", "school", "schools", "college",
        "faculty", "academics", "academic", "education", "medicine",
        "health-sciences", "clinical", "research", "specialties",
    )
    paths: set[str] = set()
    for slug in slugs:
        for prefix in prefixes:
            paths.add(f"{root}/{prefix}/{slug}" if prefix else f"{root}/{slug}")
            paths.add(f"{root}/{slug}/faculty")
            paths.add(f"{root}/{slug}/people")
    return sorted(paths)


def site_search_department_urls(host: str, region: str, specialty: str, terms: list[str]) -> list[dict[str, str]]:
    primary = terms[0] if terms else specialty
    queries = [
        f"site:{host} {primary} faculty",
        f"site:{host} {specialty} department faculty",
        f"site:{host} {primary} people directory",
        f"site:{host} {primary} academic staff",
        f"site:{host} {region} {primary} faculty",
    ]
    results: list[dict[str, str]] = []
    seen: set[str] = set()
    for query in queries:
        for item in ddg_search(query):
            url = normalize_url(item["url"])
            if url and url not in seen:
                seen.add(url)
                item["url"] = url
                item["query"] = query
                results.append(item)
    return results


def discover_department_pages(
    institution: Institution,
    region: str,
    specialty: str,
    terms: list[str],
    disallowed_paths: list[str],
) -> tuple[list[PageCandidate], list[str], dict[str, str]]:
    session = make_session()
    official_host = institution.host
    candidates: dict[str, PageCandidate] = {}
    page_cache: dict[str, str] = {}
    log: list[str] = []

    def add_candidate(url: str, title: str, source: str, page_text: str = "") -> None:
        normalized = normalize_url(url)
        if not normalized or not related_official_domain(normalized, official_host):
            return
        if not path_allowed(normalized, disallowed_paths):
            return
        evidence = f"{normalized} {title} {page_text[:2500]}"
        matched = text_matches_terms(evidence, terms)
        if not matched:
            return
        score = relevance_score(normalized, title, page_text, terms)
        if score <= 0:
            return
        item = PageCandidate(normalized, clean_text(title), matched, source, score)
        existing = candidates.get(normalized)
        if not existing or item.score > existing.score:
            candidates[normalized] = item

    html, final_url, error = fetch_html(session, institution.official_url)
    if html and final_url:
        page_cache[final_url] = html
        soup = BeautifulSoup(html, "html.parser")
        homepage_text = clean_text(soup.get_text(" ", strip=True))
        add_candidate(final_url, soup.title.get_text(" ", strip=True) if soup.title else "", "homepage", homepage_text)
        for anchor in soup.find_all("a", href=True):
            href = normalize_url(urljoin(final_url, anchor.get("href", "")))
            link_text = clean_text(anchor.get_text(" ", strip=True))
            combined = f"{href or ''} {link_text}"
            if href and (text_matches_terms(combined, terms) or any(word in combined.lower() for word in DEPARTMENT_PAGE_WORDS)):
                add_candidate(href, link_text, "homepage_link", link_text)
        log.append("Homepage links checked.")
    else:
        log.append(f"Homepage unavailable: {error or institution.official_url}")

    for item in site_search_department_urls(official_host, region, specialty, terms):
        add_candidate(item["url"], item.get("title", ""), "site_search", item.get("body", ""))
    log.append("Official-site search checked.")

    sitemap_checked = 0
    for sitemap in discover_sitemaps(session, institution.official_url):
        response, _, _ = fetch_response(session, sitemap)
        if not response:
            continue
        content = response.text
        if "xml" not in response.headers.get("Content-Type", "").lower() and "<url" not in content.lower():
            continue
        for found_url in extract_sitemap_urls(content):
            sitemap_checked += 1
            if found_url.lower().endswith(".xml"):
                nested_response, _, _ = fetch_response(session, found_url)
                if nested_response:
                    for nested_url in extract_sitemap_urls(nested_response.text):
                        add_candidate(nested_url, "", "nested_sitemap")
            else:
                add_candidate(found_url, "", "sitemap")
    log.append(f"Sitemap URLs checked: {sitemap_checked}")

    for candidate_url in common_department_paths(institution.official_url, terms):
        html, final_candidate, _ = fetch_html(session, candidate_url)
        if not html or not final_candidate:
            continue
        if not related_official_domain(final_candidate, official_host):
            continue
        soup = BeautifulSoup(html, "html.parser")
        title = clean_text(soup.title.get_text(" ", strip=True) if soup.title else "")
        text = clean_text(soup.get_text(" ", strip=True))
        page_cache[final_candidate] = html
        add_candidate(final_candidate, title, "common_path", text)
    log.append("Common department paths checked.")

    ordered = sorted(candidates.values(), key=lambda item: (-item.score, item.url))
    return ordered, log, page_cache


# ==================================================
# 8. Faculty-page discovery
# ==================================================

NEXT_LINK_WORDS = {"next", "next page", "more", "more results", "load more", ">"}


def find_pagination_links(soup: BeautifulSoup, base_url: str) -> list[str]:
    found: dict[str, None] = {}
    for link in soup.find_all(["a", "link"], rel=True):
        rels = [str(item).lower() for item in (link.get("rel") or [])]
        if "next" in rels:
            target = normalize_url(urljoin(base_url, link.get("href", "")))
            if target:
                found[target] = None
    for anchor in soup.find_all("a", href=True):
        text = clean_text(anchor.get_text(" ", strip=True)).lower()
        aria = clean_text(anchor.get("aria-label", "")).lower()
        if text.isdigit() or text in NEXT_LINK_WORDS or aria in NEXT_LINK_WORDS or "next" in aria:
            target = normalize_url(urljoin(base_url, anchor.get("href", "")))
            if target and target != normalize_url(base_url):
                found[target] = None
    return list(found.keys())


def looks_faculty_relevant(url: str, link_text: str, terms: list[str]) -> bool:
    combined = f"{url} {link_text}".lower()
    return bool(text_matches_terms(combined, terms)) or any(word in combined for word in FACULTY_PAGE_WORDS)


PROFILE_HINTS = (
    "/profile", "/profiles", "/people", "/person", "/faculty", "/staff",
    "/directory", "/bio", "/biography",
)


def looks_like_profile_url(url: str, link_text: str = "") -> bool:
    combined = f"{url} {link_text}".lower()
    if not any(hint in combined for hint in PROFILE_HINTS):
        return False
    if any(bad in combined for bad in ("browse?", "search?", "filter=", "page=", "department=")):
        return False
    return True


# ==================================================
# 9. Faculty and role validation
# ==================================================

CREDENTIALS = {
    "MD", "DO", "PHD", "DPHIL", "MPH", "MSC", "MS", "MA", "MBBS", "MBCHB",
    "RN", "DPT", "PT", "DNP", "MSN", "FACOG", "FRCOG", "FACS", "FAAP",
    "MBA", "JD", "PHARMD", "DDS", "DMD", "SCD", "EDD", "BSN", "CNM",
    "MHA", "FACC", "FRCP", "FRCS", "MRCP", "MPHIL", "BA", "BS", "MPT",
}

NAME_PARTICLES = {
    "de", "del", "della", "da", "di", "van", "von", "der", "den",
    "bin", "binte", "al", "el", "la", "le", "dos", "das", "du",
    "ter", "ten", "st", "mc", "mac", "y", "ibn",
}

NAME_STOPWORDS = {
    "and", "the", "for", "of", "our", "all", "view", "more", "home",
    "current", "research", "scholarly", "interests", "education",
    "contact", "alternate", "additional", "info", "information",
    "office", "department", "departments", "faculty", "staff", "people",
    "directory", "profile", "profiles", "provider", "providers",
    "school", "college", "university", "institute", "center", "centre",
    "division", "section", "program", "programme", "affairs", "dean",
    "admissions", "business", "medicine", "health", "hospital", "clinic",
    "laboratory", "lab", "news", "events", "about", "overview",
    "publications", "biography", "administrative", "assistant",
    "coordinator", "manager", "team", "student", "students", "alumni",
    "search", "menu", "clinical", "trials", "care", "patient", "services",
}

NAME_TOKEN_RE = re.compile(r"^[A-Za-z\u00C0-\u024F'.-]+$")

ALLOWED_TITLE_PATTERNS = [
    r"\bclinical\s+associate\s+professor\b",
    r"\bclinical\s+assistant\s+professor\b",
    r"\bclinical\s+professor\b",
    r"\bsenior\s+lecturer\b",
    r"\bassociate\s+professor\b",
    r"\bassistant\s+professor\b",
    r"\bprofessor\b",
    r"\bclinical\s+instructor\b",
    r"\binstructor\b",
    r"\blecturer\b",
    r"\bfaculty\b",
    r"\bteaching\s+faculty\b",
    r"\bresearch\s+faculty\b",
    r"\bacademic\s+researcher\b",
    r"\bdepartment\s+chair\b",
    r"\bdivision\s+chief\b",
    r"\bprogram\s+director\b",
    r"\bprogramme\s+director\b",
    r"\bchair(?:person)?\s+of\s+(?:the\s+)?department\b",
]

EXCLUSION_REASON_PATTERNS = [
    (r"\bemeritus\b|\bemerita\b", "Emeritus faculty"),
    (r"\badjunct\b", "Adjunct faculty"),
    (r"\baffiliated\s+faculty\b|\bcourtesy\s+faculty\b", "Affiliated or courtesy faculty"),
    (r"\bvisiting\s+(?:faculty|professor|scholar)\b", "Visiting faculty"),
    (r"\bresident\b", "Resident"),
    (
        r"\b(?:clinical\s+|postdoctoral\s+|research\s+)?fellow\b"
        r"(?!\s+of\s+the\s+(?:american|royal|national|international)\b)",
        "Fellow",
    ),
    (r"\bfellowship\b", "Fellowship role"),
    (r"\bpostdoctoral\b|\bpostdoc\b", "Postdoctoral role"),
    (r"\bresearch\s+assistant\b|\bgraduate\s+assistant\b|\bteaching\s+assistant\b", "Assistant role"),
    (r"\bresearch\s+coordinator\b|\bprogram\s+coordinator\b|\bdepartment\s+coordinator\b|\bcoordinator\b", "Coordinator role"),
    (r"\bprogram\s+manager\b|\boffice\s+manager\b", "Manager role"),
    (r"\badministrative\s+assistant\b|\badministrative\s+associate\b|\bexecutive\s+assistant\b", "Administrative staff"),
    (r"\bnurse\s+practitioner\b|\bphysician\s+assistant\b|\bmidwife\b", "Non-faculty clinical role"),
    (r"\btechnician\b|\blab\s+assistant\b|\bsupport\s+staff\b|\boffice\s+staff\b", "Support staff"),
    (r"\bstudent\b", "Student"),
]

ALLOWED_TITLE_RE = [re.compile(pattern, re.I) for pattern in ALLOWED_TITLE_PATTERNS]
EXCLUSION_REASON_RE = [(re.compile(pattern, re.I), reason) for pattern, reason in EXCLUSION_REASON_PATTERNS]


def strip_credentials(value: str) -> str:
    parts = [part.strip() for part in value.split(",")]
    while len(parts) > 1:
        compact = re.sub(r"[^A-Za-z]", "", parts[-1]).upper()
        if compact in CREDENTIALS:
            parts.pop()
        else:
            break
    return ", ".join(parts)


def clean_name(value: str) -> str:
    value = clean_text(value)
    value = re.sub(r"^(?:Dr\.?|Prof\.?|Professor|Mr\.?|Ms\.?|Mrs\.?)\s+", "", value, flags=re.I)
    value = re.sub(r"\s+[|\-:]\s+.*$", "", value)
    value = strip_credentials(value)
    return value.strip(" ,;|-:")


def valid_name(value: str) -> bool:
    name = clean_name(value)
    if not 4 <= len(name) <= 90:
        return False
    if "@" in name or any(char.isdigit() for char in name):
        return False
    if re.search(r"\b(?:our team|et al|read more|learn more)\b", name, flags=re.I):
        return False
    tokens = [token for token in name.replace(",", " ").split() if token]
    if not 2 <= len(tokens) <= 6:
        return False
    strong = 0
    for token in tokens:
        core = token.strip(".,'-")
        if not core:
            return False
        lowered = core.lower()
        if lowered in NAME_PARTICLES:
            continue
        if lowered in NAME_STOPWORDS:
            return False
        if not core[0].isupper():
            return False
        if not NAME_TOKEN_RE.match(core):
            return False
        strong += 1
    return strong >= 2


def normalize_person_name(name: str) -> str:
    value = clean_name(name)
    value = re.sub(r"\b(?:" + "|".join(sorted(CREDENTIALS)) + r")\b\.?", "", value, flags=re.I)
    value = re.sub(r"[^A-Za-z\u00C0-\u024F' -]+", " ", value)
    return clean_text(value).casefold()


def excluded_role_reason(text: str) -> str | None:
    cleaned = clean_text(text)
    for pattern, reason in EXCLUSION_REASON_RE:
        if pattern.search(cleaned):
            return reason
    return None


def matched_allowed_title(text: str) -> str | None:
    cleaned = clean_text(text)
    for pattern in ALLOWED_TITLE_RE:
        match = pattern.search(cleaned)
        if match:
            return match.group(0).strip()
    return None


def roster_name_match(candidate: str, roster_names: set[str]) -> bool:
    normalized = normalize_person_name(candidate)
    if normalized in roster_names:
        return True
    parts = normalized.split()
    if len(parts) >= 2:
        first_last = f"{parts[0]} {parts[-1]}"
        for roster_name in roster_names:
            roster_parts = roster_name.split()
            if len(roster_parts) >= 2 and first_last == f"{roster_parts[0]} {roster_parts[-1]}":
                return True
    return False


# ==================================================
# 10. Name and email extraction
# ==================================================

CANDIDATE_NODE_SELECTOR = (
    "article, li, tr, [class*='faculty' i], [class*='person' i], "
    "[class*='profile' i], [class*='staff' i], [class*='card' i], "
    "[class*='result' i], [class*='member' i], [class*='directory' i]"
)

TITLE_SELECTORS = (
    "[class*='title' i]", "[class*='role' i]", "[class*='position' i]",
    "[class*='rank' i]", "[class*='appointment' i]", "[class*='job' i]",
)

NAME_SELECTORS = (
    "[itemprop='name']", "[class*='name' i]", "h1", "h2", "h3", "h4",
    "strong", "b",
)

EMAIL_RE = re.compile(r"\b[A-Z0-9._%+\-]+@[A-Z0-9.\-]+\.[A-Z]{2,63}\b", re.I)

OBFUSCATION_REPLACEMENTS = [
    (r"\s*\[\s*at\s*\]\s*", "@"),
    (r"\s*\(\s*at\s*\)\s*", "@"),
    (r"\s+at\s+", "@"),
    (r"\s*\[\s*dot\s*\]\s*", "."),
    (r"\s*\(\s*dot\s*\)\s*", "."),
    (r"\s+dot\s+", "."),
]


def decode_visible_emails(text: str) -> set[str]:
    original = text or ""
    values = {email.lower().strip(".,;:()[]<>") for email in EMAIL_RE.findall(original)}
    candidate = clean_text(original)
    for pattern, replacement in OBFUSCATION_REPLACEMENTS:
        candidate = re.sub(pattern, replacement, candidate, flags=re.I)
    values.update(email.lower().strip(".,;:()[]<>") for email in EMAIL_RE.findall(candidate))
    return {trim_run_on_email(email) for email in values if email}


def trim_run_on_email(email: str) -> str:
    local, sep, domain = email.partition("@")
    if not sep:
        return email
    labels = domain.split(".")
    while len(labels) > 2 and labels[-1][:1].isupper():
        labels.pop()
    return f"{local}@{'.'.join(labels)}".lower().strip(".,;:()[]<>")


def extract_name_from_node(node: Tag) -> str | None:
    for selector in NAME_SELECTORS:
        for child in node.select(selector):
            candidate = clean_name(child.get_text(" ", strip=True))
            if valid_name(candidate):
                return candidate
    for anchor in node.select("a[href]"):
        candidate = clean_name(anchor.get_text(" ", strip=True))
        if valid_name(candidate):
            return candidate
    return None


def collect_names_in_node(node: Tag, limit: int = 6) -> set[str]:
    names: set[str] = set()
    for selector in (*NAME_SELECTORS, "a[href]"):
        for child in node.select(selector):
            candidate = clean_name(child.get_text(" ", strip=True))
            if valid_name(candidate):
                names.add(normalize_person_name(candidate))
                if len(names) > limit:
                    return names
    return names


def extract_title_text(node: Tag, full_text: str, name: str | None) -> str:
    for selector in TITLE_SELECTORS:
        element = node.select_one(selector)
        if element:
            value = clean_text(element.get_text(" ", strip=True))
            if 3 <= len(value) <= 220:
                return value
    if name:
        index = full_text.find(name)
        if index != -1:
            return full_text[index + len(name):index + len(name) + 220]
    return full_text[:220]


def page_has_js_only_signals(soup: BeautifulSoup, text: str) -> bool:
    scripts = soup.find_all("script")
    app_roots = soup.select("#root, #app, [data-reactroot], [id*='__next']")
    return len(text) < 250 and (len(scripts) >= 4 or bool(app_roots))


def extract_roster_entries_from_soup(page_url: str, soup: BeautifulSoup) -> tuple[list[FacultyEntry], list[Rejection]]:
    entries: list[FacultyEntry] = []
    rejections: list[Rejection] = []
    seen: set[str] = set()

    for node in soup.select(CANDIDATE_NODE_SELECTOR):
        text = clean_text(node.get_text(" ", strip=True))
        if not 10 <= len(text) <= 2000:
            continue
        name = extract_name_from_node(node)
        if not name:
            continue
        title_text = extract_title_text(node, text, name)
        reason = excluded_role_reason(title_text)
        allowed = matched_allowed_title(title_text)
        if reason or not allowed:
            if reason:
                rejections.append(Rejection(name=name, reason=reason, source_url=page_url, detail=title_text[:220]))
            continue
        normalized = normalize_person_name(name)
        if normalized in seen:
            continue
        seen.add(normalized)
        profile_url = None
        for anchor in node.find_all("a", href=True):
            target = normalize_url(urljoin(page_url, anchor.get("href", "")))
            if target and looks_like_profile_url(target, anchor.get_text(" ", strip=True)):
                profile_url = target
                break
        entries.append(FacultyEntry(
            name=name,
            normalized_name=normalized,
            title=allowed.title(),
            source_url=page_url,
            evidence=text[:600],
            profile_url=profile_url,
        ))
    return entries, rejections


def discover_faculty_roster(
    department_pages: list[PageCandidate],
    institution: Institution,
    terms: list[str],
    delay_seconds: float,
    disallowed_paths: list[str],
    seed_cache: dict[str, str] | None = None,
) -> tuple[list[FacultyEntry], list[str], list[Rejection], dict[str, str], list[str], list[str]]:
    session = make_session()
    queue: deque[str] = deque(page.url for page in department_pages)
    visited: set[str] = set()
    roster: dict[str, FacultyEntry] = {}
    faculty_pages: list[str] = []
    rejections: list[Rejection] = []
    page_cache: dict[str, str] = dict(seed_cache or {})
    log: list[str] = []
    blocked: list[str] = []

    while queue:
        raw_url = queue.popleft()
        normalized = normalize_url(raw_url)
        if not normalized or normalized in visited:
            continue
        if not related_official_domain(normalized, institution.host):
            continue
        if not path_allowed(normalized, disallowed_paths):
            log.append(f"Skipped by robots.txt: {normalized}")
            continue
        visited.add(normalized)

        if is_pdf_url(normalized):
            text, error = fetch_pdf_text(session, normalized)
            if error:
                blocked.append(f"{normalized}: {error}")
            elif text and text_matches_terms(text, terms):
                faculty_pages.append(normalized)
            continue

        html = page_cache.get(normalized)
        final_url = normalized
        if html is None:
            html, final_url, error = fetch_html(session, normalized)
            if not html or not final_url:
                blocked.append(f"{normalized}: {error or 'unavailable'}")
                continue
            if not related_official_domain(final_url, institution.host):
                continue
            page_cache[final_url] = html

        soup = BeautifulSoup(html, "html.parser")
        for tag in soup(["script", "style", "noscript", "nav", "footer", "form"]):
            tag.decompose()
        title = clean_text(soup.title.get_text(" ", strip=True) if soup.title else "")
        page_text = clean_text(soup.get_text(" ", strip=True))
        combined_header = f"{final_url} {title}".lower()
        if any(word in combined_header for word in FACULTY_PAGE_WORDS):
            faculty_pages.append(final_url)

        if page_has_js_only_signals(soup, page_text):
            log.append(f"Possible JavaScript-only directory: {final_url}")

        if text_matches_terms(f"{final_url} {title} {page_text}", terms):
            found_entries, found_rejections = extract_roster_entries_from_soup(final_url, soup)
            for entry in found_entries:
                roster.setdefault(entry.normalized_name, entry)
            rejections.extend(found_rejections)

        for page_link in find_pagination_links(soup, final_url):
            if page_link not in visited and related_official_domain(page_link, institution.host):
                queue.append(page_link)

        for anchor in soup.find_all("a", href=True):
            link = normalize_url(urljoin(final_url, anchor.get("href", "")))
            if not link or link in visited:
                continue
            if not related_official_domain(link, institution.host):
                continue
            if not path_allowed(link, disallowed_paths):
                continue
            link_text = clean_text(anchor.get_text(" ", strip=True))
            if looks_faculty_relevant(link, link_text, terms):
                queue.append(link)

        log.append(f"[{len(visited)} checked] {final_url}")
        if delay_seconds > 0:
            time.sleep(delay_seconds)

    return list(roster.values()), sorted(set(faculty_pages)), rejections, page_cache, log, blocked


def discover_profile_links(
    page_cache: dict[str, str],
    institution_host: str,
    roster_entries: list[FacultyEntry],
) -> list[dict[str, object]]:
    roster_names = {entry.normalized_name for entry in roster_entries}
    links: dict[str, dict[str, object]] = {}
    for page_url, html in page_cache.items():
        soup = BeautifulSoup(html, "html.parser")
        for anchor in soup.find_all("a", href=True):
            target = normalize_url(urljoin(page_url, anchor.get("href", "")))
            text = clean_text(anchor.get_text(" ", strip=True))
            if not target or not related_official_domain(target, institution_host):
                continue
            if not looks_like_profile_url(target, text):
                continue
            score = 20
            if valid_name(text) and roster_name_match(text, roster_names):
                score += 60
            elif valid_name(text):
                score += 20
            item = {"url": target, "text": text, "score": score, "from": page_url}
            if target not in links or score > int(links[target]["score"]):
                links[target] = item
    for entry in roster_entries:
        if entry.profile_url and entry.profile_url not in links:
            links[entry.profile_url] = {"url": entry.profile_url, "text": entry.name, "score": 90, "from": entry.source_url}
    return sorted(links.values(), key=lambda item: (-int(item["score"]), str(item["url"])))


# ==================================================
# 11. Email validation
# ==================================================

PERSONAL_EMAIL_DOMAINS = {
    "gmail.com", "googlemail.com", "yahoo.com", "hotmail.com", "outlook.com",
    "icloud.com", "aol.com", "protonmail.com", "proton.me", "live.com",
    "msn.com", "mail.com", "pm.me", "zoho.com", "gmx.com",
}

GENERIC_EMAIL_PREFIXES = {
    "info", "contact", "admin", "office", "support", "help", "admissions",
    "enquiries", "inquiries", "webmaster", "reception", "communications",
    "media", "appointments", "appointment", "clinic", "department", "dept",
    "faculty", "frontdesk", "secretary", "generalinfo", "hello",
}

DEPARTMENT_MAILBOX_WORDS = {
    "medicine", "med", "nursing", "health", "school", "college", "dept",
    "department", "departments", "faculty", "academics", "academic",
    "enquiry", "inquiry", "general", "mail", "admin",
}

ADMIN_CONTEXT_MARKERS = (
    "administrative contact", "administrative associate", "administrative assistant",
    "administrative aide", "executive assistant", "alternate contact",
    "program coordinator", "programme coordinator", "program manager",
    "office manager", "assistant to the", "scheduling", "scheduler",
    "media inquiries", "press inquiries", "for appointments",
)

CONTACT_LABEL_RE = re.compile(r"(?:e-?mail|contact|reach(?:\s+\w+)?\s+at|correspondence)\W{0,20}$", re.I)


def compact_local(value: str) -> str:
    return re.sub(r"[^a-z0-9]", "", value.lower())


def email_domain_belongs(email_domain: str, official_host: str) -> bool:
    email_domain = email_domain.lower().removeprefix("www.")
    return (
        email_domain == official_host
        or email_domain.endswith("." + official_host)
        or official_host.endswith("." + email_domain)
        or organization_root(email_domain) == organization_root(official_host)
    )


def classify_email(email: str, official_host: str) -> tuple[bool, str | None]:
    email = trim_run_on_email(email)
    if not EMAIL_RE.fullmatch(email):
        return False, "Malformed email"
    local, domain = email.split("@", 1)
    local_compact = compact_local(local)
    if domain in PERSONAL_EMAIL_DOMAINS:
        return False, "Personal email domain"
    if local_compact in GENERIC_EMAIL_PREFIXES:
        return False, "Generic email"
    if not email_domain_belongs(domain, official_host):
        return False, "Outside official domain family"
    return True, None


def is_admin_context(text: str) -> bool:
    lowered = clean_text(text).lower()
    if "contact academic" in lowered:
        return False
    return any(marker in lowered for marker in ADMIN_CONTEXT_MARKERS)


def emails_in_local_block(block: Tag, block_text: str) -> set[str]:
    emails: set[str] = set()
    for anchor in block.select('a[href^="mailto:" i]'):
        href = anchor.get("href", "")
        address = href[7:].split("?", 1)[0]
        if address:
            emails.update(decode_visible_emails(f"{address} {anchor.get_text(' ', strip=True)}"))
    emails.update(decode_visible_emails(block_text))
    return emails


def ancestor_context(anchor: Tag, max_levels: int = 4, max_chars: int = 500) -> str:
    current: Tag = anchor
    for _ in range(max_levels):
        parent = current.parent
        if not isinstance(parent, Tag):
            break
        current = parent
        text = clean_text(current.get_text(" ", strip=True))
        if len(text) >= 40:
            return text[:max_chars]
    return clean_text(current.get_text(" ", strip=True))[:max_chars]


def extract_emails_with_context(soup: BeautifulSoup | Tag, page_text: str) -> dict[str, list[dict[str, str]]]:
    occurrences: dict[str, list[dict[str, str]]] = {}

    def add(email: str, context: str, source: str, before: str = "") -> None:
        email = trim_run_on_email(email)
        if not email:
            return
        occurrences.setdefault(email, []).append({
            "context": clean_text(context),
            "source": source,
            "before": clean_text(before),
        })

    for anchor in soup.select('a[href^="mailto:" i]'):
        href = anchor.get("href", "")
        address = href[7:].split("?", 1)[0].strip()
        if not address:
            continue
        context = ancestor_context(anchor)
        for email in decode_visible_emails(f"{address} {anchor.get_text(' ', strip=True)}"):
            add(email, context, "mailto", context)

    for match in EMAIL_RE.finditer(page_text or ""):
        raw = trim_run_on_email(match.group(0))
        start = max(0, match.start() - 260)
        before = page_text[start:match.start()]
        context = page_text[start: min(len(page_text), match.end() + 80)]
        add(raw, context, "text", before)

    decoded = decode_visible_emails(page_text)
    for email in decoded:
        if email not in occurrences:
            add(email, page_text[:700], "obfuscated", page_text[:700])

    return occurrences


def is_displayed_contact(entries: list[dict[str, str]]) -> bool:
    for entry in entries:
        if entry["source"] == "mailto":
            return True
        before = entry.get("before", "")[-80:]
        if CONTACT_LABEL_RE.search(before):
            return True
        if entry["source"] == "obfuscated" and re.search(r"\b(e-?mail|contact)\b", entry.get("context", ""), flags=re.I):
            return True
    return False


# ==================================================
# 12. Generic fallback
# ==================================================

def is_generic_department_local(local: str, terms: list[str]) -> bool:
    compact = compact_local(local)
    if compact in GENERIC_EMAIL_PREFIXES or compact in DEPARTMENT_MAILBOX_WORDS:
        return True
    return any(compact_local(term) == compact for term in terms)


def find_generic_department_email(
    department_pages: list[PageCandidate],
    institution: Institution,
    terms: list[str],
    page_cache: dict[str, str],
) -> Contact | None:
    session = make_session()
    for page in department_pages:
        html = page_cache.get(page.url)
        final_url = page.url
        if html is None:
            html, final_url, _ = fetch_html(session, page.url)
        if not html or not final_url:
            continue
        soup = BeautifulSoup(html, "html.parser")
        for tag in soup(["nav", "footer", "script", "style", "noscript"]):
            tag.decompose()
        text = clean_text(soup.get_text(" ", strip=True))
        if not text_matches_terms(f"{final_url} {text}", terms):
            continue
        for email in sorted(decode_visible_emails(text)):
            if "@" not in email:
                continue
            local, domain = email.split("@", 1)
            if is_generic_department_local(local, terms) and email_domain_belongs(domain, institution.host):
                return Contact(
                    name="Department Contact",
                    email=email,
                    institution=institution.name,
                    source_url=final_url,
                    method="Generic department fallback",
                    strength=9,
                )
    return None


# ==================================================
# 13. Deduplication
# ==================================================

def deduplicate_contacts(contacts: list[Contact]) -> list[Contact]:
    by_email: dict[str, Contact] = {}
    for contact in contacts:
        email_key = contact.email.strip().lower()
        existing = by_email.get(email_key)
        if not existing or contact.strength < existing.strength:
            by_email[email_key] = contact

    by_exact_row: dict[tuple[str, str], Contact] = {}
    for contact in by_email.values():
        key = (normalize_person_name(contact.name), contact.email.strip().lower())
        existing = by_exact_row.get(key)
        if not existing or contact.strength < existing.strength:
            by_exact_row[key] = contact

    return sorted(by_exact_row.values(), key=lambda item: (item.name.casefold(), item.email.casefold()))


def final_dataframe(contacts: list[Contact]) -> pd.DataFrame:
    rows = [contact.final_row() for contact in deduplicate_contacts(contacts)]
    frame = pd.DataFrame(rows, columns=["Name", "Email"])
    if frame.empty:
        return frame
    frame = frame.dropna()
    frame = frame[(frame["Name"].str.strip() != "") & (frame["Email"].str.strip() != "")]
    frame = frame.drop_duplicates().sort_values(["Name", "Email"], kind="stable")
    return frame.reset_index(drop=True)


# ==================================================
# 14. Institution processing pipeline
# ==================================================

def parse_profile_page(
    url: str,
    html: str,
    institution: Institution,
    roster_entries: list[FacultyEntry],
) -> tuple[list[Contact], list[Rejection]]:
    roster_names = {entry.normalized_name for entry in roster_entries}
    roster_by_name = {entry.normalized_name: entry for entry in roster_entries}
    soup = BeautifulSoup(html, "html.parser")
    for tag in soup(["script", "style", "noscript", "nav", "footer", "form"]):
        tag.decompose()
    page_text = clean_text(soup.get_text(" ", strip=True))

    name = None
    for selector in ("h1", "[itemprop='name']", "[class*='profile-name' i]", "[class*='faculty-name' i]", "[class*='person-name' i]"):
        for element in soup.select(selector):
            candidate = clean_name(element.get_text(" ", strip=True))
            if valid_name(candidate):
                name = candidate
                break
        if name:
            break
    if not name and soup.title:
        for part in re.split(r"\s+[|\-:]\s+", clean_text(soup.title.get_text(" ", strip=True))):
            candidate = clean_name(part)
            if valid_name(candidate):
                name = candidate
                break

    if not name:
        return [], []
    if not roster_name_match(name, roster_names):
        return [], [Rejection(name=name, reason="Not on approved roster", source_url=url)]

    matched_entry = roster_by_name.get(normalize_person_name(name))
    display_name = matched_entry.name if matched_entry else clean_name(name)
    contacts: list[Contact] = []
    rejections: list[Rejection] = []
    contexts = extract_emails_with_context(soup, page_text)
    for email, occurrences in sorted(contexts.items()):
        if any(is_admin_context(item["context"]) for item in occurrences):
            rejections.append(Rejection(display_name, "Administrative or alternate contact email", url, email))
            continue
        if not is_displayed_contact(occurrences):
            rejections.append(Rejection(display_name, "Email not shown as a contact field", url, email))
            continue
        ok, reason = classify_email(email, institution.host)
        if ok:
            contacts.append(Contact(display_name, email, institution.name, url, "Official personal profile", 0))
        elif reason:
            rejections.append(Rejection(display_name, reason, url, email))
    if not contacts:
        rejections.append(Rejection(display_name, "No visible institutional email", url))
    return contacts, rejections


def crawl_profiles(
    profile_links: list[dict[str, object]],
    institution: Institution,
    roster_entries: list[FacultyEntry],
    delay_seconds: float,
    disallowed_paths: list[str],
) -> tuple[list[Contact], list[Rejection], list[str], list[str]]:
    session = make_session()
    contacts: list[Contact] = []
    rejections: list[Rejection] = []
    log: list[str] = []
    blocked: list[str] = []
    for index, link in enumerate(profile_links, start=1):
        url = str(link["url"])
        if not path_allowed(url, disallowed_paths):
            log.append(f"Skipped by robots.txt: {url}")
            continue
        html, final_url, error = fetch_html(session, url)
        if not html or not final_url:
            blocked.append(f"{url}: {error or 'unavailable'}")
            continue
        if not related_official_domain(final_url, institution.host):
            continue
        found_contacts, found_rejections = parse_profile_page(final_url, html, institution, roster_entries)
        contacts.extend(found_contacts)
        rejections.extend(found_rejections)
        log.append(f"{final_url}: {len(found_contacts)} contact(s)")
        if delay_seconds > 0 and index < len(profile_links):
            time.sleep(delay_seconds)
    return contacts, rejections, log, blocked


def extract_card_level_contacts(
    roster_entries: list[FacultyEntry],
    institution: Institution,
    page_cache: dict[str, str],
    already_covered: set[str],
) -> tuple[list[Contact], list[Rejection]]:
    contacts: list[Contact] = []
    rejections: list[Rejection] = []
    pending = [entry for entry in roster_entries if entry.normalized_name not in already_covered]
    by_page: dict[str, list[FacultyEntry]] = {}
    for entry in pending:
        by_page.setdefault(entry.source_url, []).append(entry)

    for page_url, entries in by_page.items():
        html = page_cache.get(page_url)
        if not html:
            continue
        soup = BeautifulSoup(html, "html.parser")
        wanted = {entry.normalized_name: entry for entry in entries}
        matched: set[str] = set()
        for node in soup.select(CANDIDATE_NODE_SELECTOR):
            node_name = extract_name_from_node(node)
            if not node_name:
                continue
            normalized = normalize_person_name(node_name)
            entry = wanted.get(normalized)
            if not entry or normalized in matched:
                continue
            block_text = clean_text(node.get_text(" ", strip=True))
            if is_admin_context(block_text):
                continue
            if len(collect_names_in_node(node)) != 1:
                continue
            matched.add(normalized)
            emails = emails_in_local_block(node, block_text)
            valid_found = False
            for email in sorted(emails):
                ok, reason = classify_email(email, institution.host)
                if ok:
                    valid_found = True
                    contacts.append(Contact(entry.name, email, institution.name, page_url, "Faculty directory card", 1))
                elif reason:
                    rejections.append(Rejection(entry.name, reason, page_url, email))
            if not valid_found:
                rejections.append(Rejection(entry.name, "No visible institutional email", page_url))
        for entry in entries:
            if entry.normalized_name not in matched:
                rejections.append(Rejection(entry.name, "No precise local card match", page_url))
    return contacts, rejections


def extract_pdf_contacts(
    department_pages: list[PageCandidate],
    institution: Institution,
    terms: list[str],
) -> tuple[list[Contact], list[Rejection]]:
    session = make_session()
    contacts: list[Contact] = []
    rejections: list[Rejection] = []
    for page in department_pages:
        if not is_pdf_url(page.url):
            continue
        text, error = fetch_pdf_text(session, page.url)
        if error or not text or not text_matches_terms(text, terms):
            continue
        chunks = re.split(r"\n|(?<=\.)\s{2,}", text)
        for chunk in chunks:
            cleaned = clean_text(chunk)
            if not (8 <= len(cleaned) <= 500):
                continue
            emails = decode_visible_emails(cleaned)
            if not emails:
                continue
            possible_name = None
            for candidate in re.findall(r"\b[A-Z][A-Za-z'.-]+(?:\s+[A-Z][A-Za-z'.-]+){1,4}\b", cleaned):
                if valid_name(candidate):
                    possible_name = clean_name(candidate)
                    break
            if not possible_name:
                continue
            title_text = cleaned[:240]
            reason = excluded_role_reason(title_text)
            allowed = matched_allowed_title(title_text)
            if reason or not allowed:
                rejections.append(Rejection(possible_name, reason or "No current faculty title", page.url, cleaned[:180]))
                continue
            if is_admin_context(cleaned):
                rejections.append(Rejection(possible_name, "Administrative context", page.url, cleaned[:180]))
                continue
            for email in emails:
                ok, email_reason = classify_email(email, institution.host)
                if ok:
                    contacts.append(Contact(possible_name, email, institution.name, page.url, "Official PDF", 2))
                elif email_reason:
                    rejections.append(Rejection(possible_name, email_reason, page.url, email))
    return contacts, rejections


def process_institution(
    institution: Institution,
    country: str,
    region: str,
    specialty: str,
    custom_keywords: str,
    delay_seconds: float,
) -> tuple[list[Contact], InstitutionReport]:
    terms = resolve_terms(specialty, custom_keywords)
    session = make_session()
    report = InstitutionReport(institution=institution.name, status="Manual review required", official_url=institution.official_url)

    robots_text = fetch_robots_txt(session, institution.official_url)
    disallowed_paths = parse_disallowed_paths(robots_text or "")
    if robots_text:
        report.notes.append("robots.txt checked")

    department_pages, department_log, seed_cache = discover_department_pages(
        institution=institution,
        region=region,
        specialty=specialty,
        terms=terms,
        disallowed_paths=disallowed_paths,
    )
    report.department_pages = len(department_pages)
    report.notes.extend(department_log[:5])
    if not department_pages:
        report.status = "Relevant department not found"
        return [], report

    roster_entries, faculty_pages, role_rejections, page_cache, crawl_log, blocked = discover_faculty_roster(
        department_pages=department_pages,
        institution=institution,
        terms=terms,
        delay_seconds=delay_seconds,
        disallowed_paths=disallowed_paths,
        seed_cache=seed_cache,
    )
    report.faculty_roster_entries = len(roster_entries)
    report.pages_checked = len(crawl_log)
    report.blocked_or_unreadable.extend(blocked)
    report.rejections.extend(role_rejections)
    report.notes.extend(crawl_log[:8])

    if not roster_entries:
        if any("JavaScript-only" in line for line in crawl_log):
            report.status = "JavaScript-only directory"
        elif blocked and not crawl_log:
            report.status = "Website blocked automated access"
        else:
            report.status = "Faculty page not found"
        return [], report

    profile_links = discover_profile_links(page_cache, institution.host, roster_entries)
    profile_contacts, profile_rejections, profile_log, profile_blocked = crawl_profiles(
        profile_links=profile_links,
        institution=institution,
        roster_entries=roster_entries,
        delay_seconds=delay_seconds,
        disallowed_paths=disallowed_paths,
    )
    report.profiles_checked = len(profile_log)
    report.rejections.extend(profile_rejections)
    report.blocked_or_unreadable.extend(profile_blocked)
    report.notes.extend(profile_log[:8])

    covered_names = {normalize_person_name(contact.name) for contact in profile_contacts}
    card_contacts, card_rejections = extract_card_level_contacts(roster_entries, institution, page_cache, covered_names)
    pdf_contacts, pdf_rejections = extract_pdf_contacts(department_pages, institution, terms)
    report.rejections.extend(card_rejections)
    report.rejections.extend(pdf_rejections)

    personal_contacts = deduplicate_contacts(profile_contacts + card_contacts + pdf_contacts)
    if personal_contacts:
        report.contacts_found = len(personal_contacts)
        report.status = "Verified contacts found"
        return personal_contacts, report

    fallback = find_generic_department_email(department_pages, institution, terms, page_cache)
    if fallback:
        report.contacts_found = 1
        report.status = "Generic department contact found"
        report.notes.append("No personal faculty emails were verified; one generic department contact returned.")
        return [fallback], report

    report.status = "No public personal faculty email found"
    return [], report


# ==================================================
# 15. Streamlit interface
# ==================================================

st.set_page_config(page_title=APP_NAME, page_icon="GM", layout="wide")

st.markdown(
    """
    <style>
    .block-container { max-width: 1180px; padding-top: 2.5rem; }
    div[data-testid="stMetric"] {
        border: 1px solid #e6e8ef;
        border-radius: 8px;
        padding: 0.65rem 0.8rem;
        background: #fbfcff;
    }
    .small-note { color: #667085; font-size: 0.92rem; line-height: 1.45; }
    </style>
    """,
    unsafe_allow_html=True,
)

st.title(APP_NAME)
st.markdown(
    '<p class="small-note">Finds publicly visible official faculty work emails from official institutional sources only. '
    'The final export contains exactly two columns: Name and Email.</p>',
    unsafe_allow_html=True,
)

with st.sidebar:
    st.subheader("Request settings")
    delay_seconds = st.slider("Delay between requests", 0.1, 2.0, 0.45, 0.05)
    st.caption("All qualifying institutions, pages, and profiles are processed. Larger searches can take longer.")

if "institutions" not in st.session_state:
    st.session_state.institutions = []
if "institution_log" not in st.session_state:
    st.session_state.institution_log = []
if "selected_institution_names" not in st.session_state:
    st.session_state.selected_institution_names = []
if "contacts" not in st.session_state:
    st.session_state.contacts = []
if "reports" not in st.session_state:
    st.session_state.reports = []
if "discovery_scope" not in st.session_state:
    st.session_state.discovery_scope = None

if pycountry is None or geonamescache is None:
    st.error("Location data packages are unavailable. Install requirements.txt, then run the app again.")
    st.stop()

countries = country_choices()
country_names = [name for name, _ in countries]
country_codes = dict(countries)
default_country_index = country_names.index("United States") if "United States" in country_names else 0

with st.container(border=True):
    col_a, col_b = st.columns(2)
    with col_a:
        country = st.selectbox("Country", country_names, index=default_country_index)
        country_code = country_codes[country]
        locations = location_choices(country_code)
        location_labels = [item["label"] for item in locations]
        default_location_index = 0
        if country_code == "US":
            default_location_index = next(
                (index for index, item in enumerate(locations) if item["value"] == "Alabama" and item["kind"] == "State"),
                0,
            )
        selected_location_label = st.selectbox(
            "State / Province / Region / City",
            location_labels,
            index=default_location_index,
            key=f"location_{country_code}",
        )
        location = next(item for item in locations if item["label"] == selected_location_label)
        region = location["value"]
        region_code = location["code"]
        region_kind = location["kind"]
    with col_b:
        specialty = st.selectbox("Department / Specialty", SPECIALTIES, index=SPECIALTIES.index("Nursing"))
        custom_keywords = st.text_input("Optional additional keywords", placeholder="neonatal nursing, family health")

    discover_clicked = st.button("Discover Institutions", type="primary", use_container_width=True)

current_scope = (country, country_code, region, region_code, region_kind, specialty, custom_keywords.strip())
if st.session_state.discovery_scope and st.session_state.discovery_scope != current_scope:
    st.session_state.institutions = []
    st.session_state.institution_log = []
    st.session_state.selected_institution_names = []
    st.session_state.contacts = []
    st.session_state.reports = []
    st.session_state.discovery_scope = None

if discover_clicked:
    if specialty == "Custom Department" and not custom_keywords.strip():
        st.error("Custom Department requires at least one keyword.")
        st.stop()
    if DDGS is None:
        st.error("The ddgs package is not available. Install requirements.txt, then run the app again.")
        st.stop()
    with st.status("Discovering official institutions...", expanded=True) as status:
        institutions, institution_log = discover_institutions(
            country,
            country_code,
            region,
            region_code,
            region_kind,
            specialty,
            custom_keywords,
        )
        st.write(f"Discovered {len(institutions)} likely official institution site(s).")
        status.update(label="Institution discovery complete.", state="complete")
    st.session_state.institutions = institutions
    st.session_state.institution_log = institution_log
    st.session_state.selected_institution_names = [item.name for item in institutions]
    st.session_state.contacts = []
    st.session_state.reports = []
    st.session_state.discovery_scope = current_scope

institutions: list[Institution] = st.session_state.institutions
if institutions:
    st.subheader("Discovered Institutions")
    st.caption("Institution names are shown here. Official URLs are stored internally and visible in diagnostics.")
    names = [item.name for item in institutions]

    btn_col_1, btn_col_2, _ = st.columns([1, 1, 3])
    with btn_col_1:
        if st.button("Select All Institutions", use_container_width=True):
            st.session_state.selected_institution_names = names
    with btn_col_2:
        if st.button("Clear Selection", use_container_width=True):
            st.session_state.selected_institution_names = []

    st.session_state.selected_institution_names = [
        name for name in st.session_state.selected_institution_names if name in names
    ]
    selected_names = st.multiselect(
        "Choose institutions to search",
        options=names,
        key="selected_institution_names",
    )

    search_clicked = st.button("Search Selected Institutions", type="primary", use_container_width=True)

    if search_clicked:
        selected = [item for item in institutions if item.name in selected_names]
        if not selected:
            st.error("Select at least one institution.")
            st.stop()

        all_contacts: list[Contact] = []
        reports: list[InstitutionReport] = []
        progress = st.progress(0)
        status_box = st.empty()

        for index, institution in enumerate(selected, start=1):
            status_box.info(f"Checking {institution.name} ({index} of {len(selected)})")
            contacts, report = process_institution(
                institution=institution,
                country=country,
                region=region,
                specialty=specialty,
                custom_keywords=custom_keywords,
                delay_seconds=delay_seconds,
            )
            all_contacts.extend(contacts)
            reports.append(report)
            progress.progress(index / len(selected))

        status_box.success("Search complete.")
        st.session_state.contacts = deduplicate_contacts(all_contacts)
        st.session_state.reports = reports

contacts = st.session_state.contacts
reports = st.session_state.reports

summary_cols = st.columns(7)
summary_values = {
    "Discovered": len(st.session_state.institutions),
    "Selected": len(st.session_state.selected_institution_names),
    "Checked": len(reports),
    "With Contacts": sum(1 for report in reports if report.contacts_found > 0),
    "Contacts": len(contacts),
    "No Public Email": sum(1 for report in reports if report.status == "No public personal faculty email found"),
    "Blocked/Review": sum(1 for report in reports if report.status in {"Website blocked automated access", "JavaScript-only directory", "Manual review required"}),
}
for col, (label, value) in zip(summary_cols, summary_values.items()):
    col.metric(label, value)

if reports or contacts:
    st.subheader("Verified Faculty Contacts")
    output_frame = final_dataframe(contacts)
    if output_frame.empty:
        st.info("No verified contacts were found for the selected institutions.")
    else:
        st.dataframe(output_frame, use_container_width=True, hide_index=True)
        st.download_button(
            "Download CSV",
            data=output_frame.to_csv(index=False).encode("utf-8"),
            file_name="verified_faculty_contacts.csv",
            mime="text/csv",
            use_container_width=True,
        )

with st.expander("Diagnostics"):
    if st.session_state.institutions:
        st.markdown("**Discovered institution URLs**")
        st.dataframe(
            pd.DataFrame([
                {
                    "Institution": item.name,
                    "Official URL": item.official_url,
                    "Host": item.host,
                    "Score": item.score,
                    "Source Query": item.source_query,
                }
                for item in st.session_state.institutions
            ]),
            use_container_width=True,
            hide_index=True,
        )

    if reports:
        st.markdown("**Institution status**")
        st.dataframe(pd.DataFrame([report.as_row() for report in reports]), use_container_width=True, hide_index=True)

        rejection_rows = [
            {
                "Institution": report.institution,
                "Name": rejection.name,
                "Reason": rejection.reason,
                "Source URL": rejection.source_url,
                "Detail": rejection.detail,
            }
            for report in reports
            for rejection in report.rejections
        ]
        if rejection_rows:
            st.markdown("**Rejected records**")
            st.dataframe(pd.DataFrame(rejection_rows), use_container_width=True, hide_index=True)

        blocked_rows = [
            {"Institution": report.institution, "Page": page}
            for report in reports
            for page in report.blocked_or_unreadable
        ]
        if blocked_rows:
            st.markdown("**Blocked or unreadable pages**")
            st.dataframe(pd.DataFrame(blocked_rows), use_container_width=True, hide_index=True)

    if st.session_state.institution_log:
        st.markdown("**Institution discovery log**")
        st.code("\n".join(st.session_state.institution_log))


# ==================================================
# 16. CSV export
# ==================================================

# Export is handled by the Download CSV button above. The final DataFrame is
# always built by final_dataframe(), which returns exactly: Name, Email.
