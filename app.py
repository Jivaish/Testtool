from __future__ import annotations

import base64
import re
import time
import unicodedata
import xml.etree.ElementTree as ET
from collections import deque
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from io import BytesIO
from pathlib import Path
from typing import Callable, Iterable
from urllib.parse import parse_qs, quote_plus, unquote, urldefrag, urljoin, urlparse, urlunparse

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
    "ama-assn.", "residencyexplorer.", "residencyprogramslist.",
    "matcharesident.", "freida.", "medresidency.",
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


@st.cache_data(show_spinner=False)
def location_scope_aliases(
    country_code: str,
    region: str,
    region_code: str,
    region_kind: str,
) -> tuple[str, ...]:
    aliases = {clean_text(region)} if region else set()
    if not region or region_kind == "City" or geonamescache is None:
        return tuple(sorted((item for item in aliases if item), key=len, reverse=True))

    admin_code = clean_text(region_code).rsplit("-", 1)[-1]
    if not admin_code:
        return tuple(aliases)
    cache = geonamescache.GeonamesCache(min_city_population=500)
    for city in cache.get_cities().values():
        if city.get("countrycode") != country_code:
            continue
        if clean_text(city.get("admin1code")).casefold() != admin_code.casefold():
            continue
        name = clean_text(city.get("name"))
        if name:
            aliases.add(name)
    return tuple(sorted((item for item in aliases if item), key=len, reverse=True))


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

SPECIALTY_DISCOVERY_TERMS: dict[str, list[str]] = {
    "Obstetrics and Gynecology": [
        "obstetrics and gynecology", "obstetrics", "gynecology",
        "gynaecology", "obgyn", "ob-gyn", "ob/gyn",
    ],
    "Pediatrics": ["pediatrics", "paediatrics", "child health"],
    "Nursing": [
        "nursing", "school of nursing", "college of nursing",
        "faculty of nursing", "nursing science", "nursing faculty",
    ],
    "Physiotherapy": ["physiotherapy", "physical therapy"],
    "Cardiology": ["cardiology", "cardiovascular medicine", "cardiovascular sciences"],
    "Oncology": ["oncology", "medical oncology", "radiation oncology"],
    "Neurology": ["neurology", "neurological sciences"],
    "Psychiatry": ["psychiatry", "psychological medicine"],
    "Public Health": ["public health", "population health", "epidemiology"],
    "Pharmacy": ["pharmacy", "pharmaceutical sciences", "clinical pharmacy"],
    "Dentistry": ["dentistry", "dental medicine", "dental school"],
    "Radiology": ["radiology", "medical imaging", "diagnostic imaging"],
    "Orthopedics": ["orthopedics", "orthopaedics", "orthopedic surgery", "orthopaedic surgery"],
    "Emergency Medicine": ["emergency medicine", "emergency medical services"],
    "Custom Department": [],
}


def clean_term(value: str) -> str:
    return re.sub(r"\s+", " ", (value or "").strip().lower())


def resolve_terms(specialty: str, custom_keywords: str = "") -> list[str]:
    terms = [] if specialty == "Custom Department" else [clean_term(specialty)]
    terms.extend(SPECIALTY_TERMS.get(specialty, []))
    terms.extend(clean_term(item) for item in (custom_keywords or "").split(","))
    seen: set[str] = set()
    ordered: list[str] = []
    for term in terms:
        if term and term not in seen:
            seen.add(term)
            ordered.append(term)
    return ordered


def resolve_discovery_terms(specialty: str, custom_keywords: str = "") -> list[str]:
    terms = list(SPECIALTY_DISCOVERY_TERMS.get(specialty, [clean_term(specialty)]))
    terms.extend(clean_term(item) for item in (custom_keywords or "").split(","))
    seen: set[str] = set()
    return [term for term in terms if term and not (term in seen or seen.add(term))]


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
    evidence_url: str = ""


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


def institution_candidate_host(host: str) -> str:
    host = (host or "").lower().strip(".").removeprefix("www.")
    root = organization_root(host)
    if not host or host == root or not host.endswith("." + root):
        return root
    prefix = host[: -(len(root) + 1)]
    generic_subdomains = {
        "academic", "academics", "admissions", "apply", "blog", "catalog",
        "college", "department", "directory", "faculty", "health", "library",
        "medicine", "med", "news", "nursing", "online", "people", "research",
        "school", "som", "staff",
    }
    generic_subdomains.update(
        clean_term(term).replace("-", "")
        for terms in SPECIALTY_DISCOVERY_TERMS.values()
        for term in terms
        if re.fullmatch(r"[a-z-]+", clean_term(term))
    )
    prefix_parts = [part for part in prefix.split(".") if part]
    while prefix_parts and prefix_parts[0].replace("-", "") in generic_subdomains:
        prefix_parts.pop(0)
    if len(prefix_parts) == 1:
        campus = prefix_parts[0]
        normalized_campus = campus.replace("-", "")
        if normalized_campus not in generic_subdomains and 2 <= len(campus) <= 16:
            return f"{campus}.{root}"
    return root


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
        lines = [clean_text(line) for text in page_text for line in text.splitlines()]
        return "\n".join(line for line in lines if line), None
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


DDGS_REGION_BY_COUNTRY = {
    "AU": "au-en", "AT": "at-de", "BE": "be-fr", "BR": "br-pt",
    "CA": "ca-en", "CH": "ch-de", "DE": "de-de", "DK": "dk-da",
    "ES": "es-es", "FI": "fi-fi", "FR": "fr-fr", "GB": "uk-en",
    "HK": "hk-tzh", "IN": "in-en", "ID": "id-en", "IE": "ie-en",
    "IT": "it-it", "JP": "jp-jp", "KR": "kr-kr", "MX": "mx-es",
    "MY": "my-en", "NL": "nl-nl", "NO": "no-no", "NZ": "nz-en",
    "PH": "ph-en", "PL": "pl-pl", "PT": "pt-pt", "RU": "ru-ru",
    "SE": "se-sv", "SG": "sg-en", "TR": "tr-tr", "TW": "tw-tzh",
    "US": "us-en", "ZA": "za-en",
}


def search_region_for_country(country_code: str = "") -> str:
    return DDGS_REGION_BY_COUNTRY.get((country_code or "").upper(), "wt-wt")


def ddg_search(query: str, search_region: str = "wt-wt") -> list[dict[str, str]]:
    if DDGS is None:
        return []
    for attempt in range(2):
        results: list[dict[str, str]] = []
        try:
            with DDGS(timeout=8) as ddgs:
                for item in ddgs.text(
                    query,
                    region=search_region or "wt-wt",
                    backend="auto",
                    max_results=None,
                ):
                    href = item.get("href") or item.get("url") or ""
                    title = item.get("title") or ""
                    body = item.get("body") or item.get("snippet") or ""
                    if href:
                        results.append({"url": href, "title": title, "body": body, "query": query})
        except Exception:
            results = []
        if results:
            return results
        if attempt == 0:
            time.sleep(0.4)
    return []


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
    location = region or country
    primary_term = terms[0] if terms else specialty
    core_terms = [primary_term]
    core_terms.extend(term for term in terms[1:] if len(term.split()) == 1)
    core_terms = list(dict.fromkeys(term for term in core_terms if term))
    term_query = " OR ".join(f'"{term}"' for term in core_terms)
    location_query = f'"{location}"'
    queries = [
        f'{location_query} university official website -jobs -news',
        f'{location_query} medical school official website -jobs -news',
        f'{location_query} osteopathic medical college official',
        f'{location_query} osteopathic medical campus official',
        f'{location_query} health sciences university official website',
        f'{location_query} academic teaching hospital official website',
        f'{location_query} ({term_query}) faculty university official',
        f'{location_query} ({term_query}) medical school faculty',
        f'{location_query} ({term_query}) college faculty directory',
        f'{location_query} "{specialty}" academic department faculty',
        f'{location_query} ({term_query}) university program curriculum',
        f'{location_query} ({term_query}) medical education clinical training',
        f'{location_query} ({term_query}) clerkship clinical rotation university',
        f'{location_query} "{specialty}" required clerkship medical school curriculum',
        f'{location_query} "{specialty}" clinical curriculum faculty contact',
        f'{location_query} ({term_query}) medical students site information',
        f'{location_query} ({term_query}) medical school partnership pathway',
        f'{location_query} ({term_query}) residency fellowship academic',
        f'{location_query} ({term_query}) regional campus teaching site',
    ]
    for hint in domain_hints_for_country(country, country_code):
        queries.extend([
            f'site:{hint} "{region or country}" ({term_query}) faculty',
            f'site:{hint} "{region or country}" "{specialty}" department',
            f'site:{hint} "{region or country}" "{specialty}" curriculum clerkship',
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
    if any(
        phrase in folded
        for phrase in (
            "association of", "admissions", "near me", "school headquarters",
            "schools and programs", "schools & programs", "collegevine",
        )
    ):
        return False
    if re.search(r"\b(?:schools|universities|colleges)\b", folded):
        return False
    if re.search(r"\b(?:university|college)\b.*\bsystem\s*$", folded):
        return False
    if re.search(r"\bprogram\s*$", folded):
        return False
    if folded in {
        "university medical center", "university medical centre",
        "university hospital", "academic medical center", "academic medical centre",
        "medical center", "medical centre", "teaching hospital",
    }:
        return False
    if "top ranked university" in folded:
        return False
    if re.match(r"^(about|contact|welcome|department|division|faculty|school news|how|what|why|when|where|guide|best|top|ranking|rankings)\b", folded):
        return False
    if any(mark in folded for mark in ("http://", "https://", "www.")):
        return False
    has_identity = any(word in folded for word in STRONG_INSTITUTION_WORDS)
    has_medical_brand = any(word in folded for word in ("medicine", "health", "clinic", "cancer center", "cancer centre"))
    is_acronym = name.replace("&", "").replace(" ", "").isalnum() and name.upper() == name and len(name) <= 16
    return has_identity or has_medical_brand or (is_acronym and is_academic_domain(host))


def institution_host_matches_brand(host: str, name: str) -> bool:
    if is_academic_domain(host):
        return True
    root_label = organization_root(host).split(".", 1)[0]
    compact_host = re.sub(r"[^a-z0-9]+", "", root_label)
    name_tokens = [
        token
        for token in re.findall(r"[a-z0-9]+", fold_text(name))
        if token not in {
            "the", "of", "at", "and", "for", "university", "college", "school",
            "hospital", "health", "medical", "medicine", "institute", "center", "centre",
        }
    ]
    compact_name = "".join(name_tokens)
    acronym = "".join(token[0] for token in name_tokens if token)
    branded_host = bool(
        compact_host
        and (
            compact_host in compact_name
            or compact_name in compact_host
            or (len(acronym) >= 2 and acronym == compact_host)
            or any(len(token) >= 4 and token in compact_host for token in name_tokens)
        )
    )
    institutional_host = any(
        marker in compact_host
        for marker in (
            "university", "college", "school", "hospital", "health", "medical",
            "medicine", "clinic", "institute", "academy",
        )
    )
    return branded_host or institutional_host


def institution_name_key(name: str) -> str:
    folded = re.sub(r"^the\s+", "", fold_text(clean_institution_name_candidate(name)))
    folded = folded.replace("&", " and ")
    return re.sub(r"[^a-z0-9]+", "", folded)


def institution_name_initialism(name: str) -> str:
    ignored = {"the", "of", "at", "and", "for", "in"}
    words = [word for word in re.findall(r"[a-z0-9]+", fold_text(name)) if word not in ignored]
    return "".join(word[0] for word in words if word)


def institution_subdomain_prefix(host: str) -> str:
    root = organization_root(host)
    normalized = (host or "").lower().removeprefix("www.")
    if normalized == root or not normalized.endswith("." + root):
        return ""
    return normalized[: -(len(root) + 1)].split(".")[0]


def deduplicate_institutions(institutions: Iterable[Institution]) -> list[Institution]:
    by_name: dict[str, Institution] = {}
    for item in institutions:
        if not valid_institution_name(item.name, item.host):
            continue
        key = institution_name_key(item.name)
        if not key:
            continue
        existing = by_name.get(key)
        if not existing or (
            item.score,
            int(is_academic_domain(item.host)),
            -len(item.official_url),
        ) > (
            existing.score,
            int(is_academic_domain(existing.host)),
            -len(existing.official_url),
        ):
            by_name[key] = item
    unique_items = list(by_name.values())
    by_domain: dict[str, list[Institution]] = {}
    for item in unique_items:
        by_domain.setdefault(organization_root(item.host), []).append(item)

    merged: list[Institution] = []
    for domain_items in by_domain.values():
        scoped_items = [
            item
            for item in domain_items
            if institution_subdomain_prefix(item.host)
            and institution_subdomain_prefix(item.host) == institution_name_initialism(item.name)
        ]
        if scoped_items:
            scoped_ids = {id(item) for item in scoped_items}
            merged.extend(
                item
                for item in domain_items
                if id(item) in scoped_ids
                or institution_subdomain_prefix(item.host) == institution_name_initialism(item.name)
            )
        else:
            merged.extend(domain_items)
    return sorted(merged, key=lambda item: (-item.score, item.name.casefold()))


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
    for source_title, weight in ((homepage_title, 100),):
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
    if any(marker in text for marker in ("high school", "grades 9-12", "grades 9 through 12")):
        if not any(marker in brand_text for marker in ("university", "college", "institute", "hospital")):
            return False
    if (
        "system" in host
        or re.search(r"\b(?:university|college)\b.{0,50}\bsystem\b", brand_text)
    ) and "health system" not in brand_text:
        return False
    evidence_count = sum(word in text for word in ACADEMIC_EVIDENCE_WORDS)
    strong_name = any(word in fold_text(name) for word in STRONG_INSTITUTION_WORDS)
    if is_academic_domain(host):
        return strong_name or evidence_count >= 2
    return strong_name and evidence_count >= 2


def page_location_corpus(name: str, soup: BeautifulSoup) -> str:
    title = clean_text(soup.title.get_text(" ", strip=True) if soup.title else "")
    chunks = [name, title]
    for meta in soup.find_all("meta", content=True):
        key = clean_text(f"{meta.get('name', '')} {meta.get('property', '')}").casefold()
        if any(word in key for word in ("description", "location", "place", "address", "site_name")):
            chunks.append(clean_text(meta.get("content")))
    for script in soup.find_all("script", attrs={"type": re.compile(r"ld\+json", re.I)}):
        chunks.append(clean_text(script.string or script.get_text(" ", strip=True)))
    for node in soup.select(
        "address, footer, [itemprop*='address' i], [class*='address' i], "
        "[class*='location' i], [id*='location' i]"
    ):
        chunks.append(clean_text(node.get_text(" ", strip=True))[:2500])
    return clean_text(" ".join(chunk for chunk in chunks if chunk))


def contains_location_term(folded_corpus: str, value: str) -> bool:
    term = fold_text(value)
    if not term:
        return False
    return bool(re.search(rf"(?<![a-z0-9]){re.escape(term)}(?![a-z0-9])", folded_corpus))


def homepage_matches_location(
    name: str,
    soup: BeautifulSoup,
    host: str,
    country: str,
    country_code: str,
    region: str,
    region_code: str,
    region_kind: str,
    supporting_text: str = "",
) -> bool:
    corpus = page_location_corpus(name, soup)
    folded = fold_text(corpus)
    folded_supporting = fold_text(supporting_text)
    if region:
        if contains_location_term(folded, region) or contains_location_term(folded_supporting, region):
            return True
        if region_kind == "City":
            return False
        abbreviation = region_code.rsplit("-", 1)[-1].upper()
        if len(abbreviation) in {2, 3}:
            postal_patterns = (
                rf"(?:,\s*|\b){re.escape(abbreviation)}\s+\d{{4,6}}\b",
                rf"(?:,\s*|\b){re.escape(abbreviation)}\s+[A-Z]\d[A-Z]\s*\d[A-Z]\d\b",
            )
            return any(re.search(pattern, corpus) for pattern in postal_patterns)
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


def official_location_pages_match(
    homepage_soup: BeautifulSoup,
    official_url: str,
    host: str,
    name: str,
    country: str,
    country_code: str,
    region: str,
    region_code: str,
    region_kind: str,
) -> bool:
    root = url_root(official_url)
    if not root:
        return False
    hints = ("contact", "location", "campus", "directions", "visit")
    urls = {
        f"{root}/contact",
        f"{root}/contact-us",
        f"{root}/locations",
        f"{root}/campuses",
    }
    for anchor in homepage_soup.find_all("a", href=True):
        link = normalize_url(urljoin(official_url, anchor.get("href", "")))
        label = clean_text(anchor.get_text(" ", strip=True)).casefold()
        combined = f"{link or ''} {label}".casefold()
        if link and related_official_domain(link, host) and any(hint in combined for hint in hints):
            urls.add(link)

    def check_page(url: str) -> bool:
        page_session = make_session()
        html, final_url, _ = fetch_html(page_session, url)
        if not html or not final_url or not related_official_domain(final_url, host):
            return False
        page_soup = BeautifulSoup(html, "html.parser")
        return homepage_matches_location(
            name,
            page_soup,
            host,
            country,
            country_code,
            region,
            region_code,
            region_kind,
        )

    with ThreadPoolExecutor(max_workers=min(4, len(urls) or 1)) as executor:
        return any(executor.map(check_page, sorted(urls)))


def specialty_program_evidence(
    text: str,
    region: str,
    terms: list[str],
) -> tuple[bool, bool]:
    folded = fold_text(text)
    direct_terms = [fold_text(term) for term in terms if fold_text(term)]
    specialty_markers = (
        "department", "division", "faculty", "program", "curriculum",
        "school of", "college of", "residency", "fellowship", "clerkship",
        "course", "training", "research",
    )
    regional_markers = (
        "partnership", "pathway", "regional campus", "clinical site",
        "training site", "teaching site", "clerkship", "clinical rotation",
        "medical education", "students spend", "campus",
    )
    specialty_verified = False
    for term in direct_terms:
        start = 0
        while (position := folded.find(term, start)) >= 0:
            context = folded[max(0, position - 700): position + len(term) + 700]
            if any(marker in context for marker in specialty_markers):
                specialty_verified = True
                break
            start = position + len(term)
        if specialty_verified:
            break

    regional_program = False
    region_term = fold_text(region)
    if specialty_verified and region_term:
        regional_place_words = (
            "campus", "clinical site", "training site", "teaching site",
            "medical center", "medical centre", "hospital", "clinic",
            "program", "pathway", "rotation", "clerkship",
        )
        place_pattern = "|".join(re.escape(word) for word in regional_place_words)
        relationship_patterns = (
            rf"\b{re.escape(region_term)}\s+(?:{place_pattern})\b",
            rf"\b(?:{place_pattern})\s+(?:in|at|for|throughout)\s+{re.escape(region_term)}\b",
        )
        for pattern in relationship_patterns:
            match = re.search(pattern, folded)
            if match:
                position = match.start()
                context = folded[max(0, position - 1500): match.end() + 1500]
            else:
                continue
            if any(term in context for term in direct_terms) and any(
                marker in context for marker in regional_markers
            ):
                regional_program = True
                break
    return specialty_verified, regional_program


def official_source_specialty_evidence(
    source_url: str,
    official_host: str,
    region: str,
    terms: list[str],
) -> tuple[bool, bool]:
    normalized = normalize_url(source_url)
    if not normalized or not related_official_domain(normalized, official_host):
        return False, False
    source_session = make_session()
    if is_pdf_url(normalized):
        text, error = fetch_pdf_text(source_session, normalized)
        if error or not text:
            return False, False
        return specialty_program_evidence(text, region, terms)
    html, final_url, _ = fetch_html(source_session, normalized)
    if not html or not final_url or not related_official_domain(final_url, official_host):
        return False, False
    soup = BeautifulSoup(html, "html.parser")
    return specialty_program_evidence(soup.get_text(" ", strip=True), region, terms)


def canonical_institution_url(raw_url: str) -> str | None:
    normalized = normalize_url(raw_url)
    if not normalized:
        return None
    parsed = urlparse(normalized)
    if is_bad_external_source(normalized):
        return None
    candidate_host = institution_candidate_host(parsed.hostname or "")
    if not candidate_host:
        return None
    return f"{parsed.scheme}://{candidate_host}"


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
    discovery_terms = resolve_discovery_terms(specialty, custom_keywords)
    queries = build_institution_queries(country, country_code, region, specialty, discovery_terms)
    institutions_by_root: dict[str, Institution] = {}
    candidates_by_root: dict[str, dict[str, tuple[int, str, dict[str, str]]]] = {}
    log: list[str] = []
    search_region = search_region_for_country(country_code)

    with ThreadPoolExecutor(max_workers=min(6, len(queries))) as executor:
        search_groups = list(executor.map(lambda query: ddg_search(query, search_region), queries))

    for query, search_results in zip(queries, search_groups):
        log.append(f"{query}: {len(search_results)} result(s)")
        for result in search_results:
            candidate_url = canonical_institution_url(result["url"])
            if not candidate_url:
                continue
            host = host_of(candidate_url)
            root = institution_candidate_host(host)
            score = score_institution_result(
                result["url"],
                result["title"],
                result["body"],
                country,
                country_code,
                discovery_terms,
            )
            if score < 35:
                continue
            result_text = fold_text(f"{result['url']} {result['title']} {result['body']}")
            has_specialty_evidence = any(fold_text(term) in result_text for term in discovery_terms)
            has_region_evidence = contains_location_term(result_text, region) if region else True
            enriched_result = {
                **result,
                "candidate_url": candidate_url,
                "specialty_evidence": "1" if has_specialty_evidence else "0",
                "region_evidence": "1" if has_region_evidence else "0",
            }
            root_candidates = candidates_by_root.setdefault(root, {})
            evidence_key = normalize_url(result["url"]) or result["url"]
            existing_candidate = root_candidates.get(evidence_key)
            new_rank = (
                int(has_specialty_evidence),
                int(has_specialty_evidence and has_region_evidence),
                score,
            )
            existing_rank = (
                int(bool(existing_candidate and existing_candidate[2]["specialty_evidence"] == "1")),
                int(bool(
                    existing_candidate
                    and existing_candidate[2]["specialty_evidence"] == "1"
                    and existing_candidate[2].get("region_evidence") == "1"
                )),
                existing_candidate[0] if existing_candidate else -1000,
            )
            if not existing_candidate or new_rank > existing_rank:
                root_candidates[evidence_key] = (score, query, enriched_result)

    term_query = " OR ".join(f'"{term}"' for term in discovery_terms)
    follow_up_targets = [
        (root, payloads)
        for root, payloads in candidates_by_root.items()
        if payloads
        and not any(payload[2]["specialty_evidence"] == "1" for payload in payloads.values())
        and max(payload[0] for payload in payloads.values()) >= 45
        and any(payload[2].get("region_evidence") == "1" for payload in payloads.values())
        and is_academic_domain(root)
    ]

    def official_specialty_follow_up(
        target: tuple[str, dict[str, tuple[int, str, dict[str, str]]]],
    ) -> tuple[str, str, list[dict[str, str]]]:
        root, _ = target
        query = (
            f"site:{root} ({term_query}) "
            '(faculty OR curriculum OR clerkship OR "clinical rotation")'
        )
        return root, query, ddg_search(query, search_region)

    if follow_up_targets:
        with ThreadPoolExecutor(max_workers=min(12, len(follow_up_targets))) as executor:
            follow_up_groups = executor.map(official_specialty_follow_up, follow_up_targets)
            for root, query, results in follow_up_groups:
                accepted = 0
                root_candidates = candidates_by_root[root]
                base_candidate_url = max(
                    root_candidates.values(),
                    key=lambda payload: payload[0],
                )[2]["candidate_url"]
                for result in results:
                    normalized_result_url = normalize_url(result["url"])
                    if not normalized_result_url or not related_official_domain(normalized_result_url, root):
                        continue
                    result_text = fold_text(
                        f"{result['url']} {result['title']} {result['body']}"
                    )
                    if not any(fold_text(term) in result_text for term in discovery_terms):
                        continue
                    score = score_institution_result(
                        result["url"],
                        result["title"],
                        result["body"],
                        country,
                        country_code,
                        discovery_terms,
                    )
                    if score < 35:
                        continue
                    evidence_key = normalized_result_url
                    enriched_result = {
                        **result,
                        "candidate_url": base_candidate_url,
                        "specialty_evidence": "1",
                        "region_evidence": "1" if contains_location_term(result_text, region) else "0",
                    }
                    existing_candidate = root_candidates.get(evidence_key)
                    if not existing_candidate or score > existing_candidate[0]:
                        root_candidates[evidence_key] = (score, query, enriched_result)
                        accepted += 1
                log.append(f"Official specialty follow-up for {root}: {accepted} evidence result(s)")

    def verify_candidate(
        grouped_payload: tuple[str, list[tuple[int, str, dict[str, str]]]],
    ) -> tuple[str, Institution | None, str]:
        root, payloads = grouped_payload
        eligible_payloads = [
            payload for payload in payloads if payload[2]["specialty_evidence"] == "1"
        ]
        if not eligible_payloads:
            candidate_url = payloads[0][2]["candidate_url"]
            return root, None, f"Rejected {candidate_url}: no official search evidence for {specialty}"

        score, query, result = max(
            eligible_payloads,
            key=lambda payload: (
                int(payload[2].get("region_evidence") == "1"),
                payload[0],
            ),
        )
        candidate_url = result["candidate_url"]
        session = make_session()
        html, final_url, error = fetch_html(session, candidate_url)
        if not html or not final_url:
            message = f"Rejected {candidate_url}: homepage could not be verified ({error or 'unavailable'})"
            return root, None, message

        verification_url = canonical_institution_url(final_url) or candidate_url
        verification_host = host_of(verification_url)
        institution_host = host_of(candidate_url)
        soup = BeautifulSoup(html, "html.parser")
        name = extract_institution_name(soup, result["title"], verification_host)
        if not name:
            return root, None, f"Rejected {candidate_url}: no valid institution brand found on homepage"
        if not homepage_has_academic_identity(name, soup, verification_host):
            message = f"Rejected {candidate_url}: homepage did not verify an academic or teaching institution"
            return root, None, message
        if not institution_host_matches_brand(verification_host, name):
            message = f"Rejected {candidate_url}: domain did not match the institution brand"
            return root, None, message
        def check_evidence(
            payload: tuple[int, str, dict[str, str]],
        ) -> tuple[tuple[int, str, dict[str, str]], bool, bool]:
            payload_result = payload[2]
            specialty_match, regional_match = official_source_specialty_evidence(
                payload_result["url"],
                host_of(payload_result["url"]),
                region,
                discovery_terms,
            )
            return payload, specialty_match, regional_match

        with ThreadPoolExecutor(max_workers=min(6, len(eligible_payloads) or 1)) as executor:
            evidence_checks = list(executor.map(check_evidence, eligible_payloads))
        verified_evidence = [item for item in evidence_checks if item[1]]
        if not verified_evidence:
            message = f"Rejected {candidate_url}: official source did not verify {specialty} teaching or training"
            return root, None, message
        evidence_payload, _, regional_program_verified = max(
            verified_evidence,
            key=lambda item: (
                int(item[2]),
                int(item[0][2].get("region_evidence") == "1"),
                item[0][0],
            ),
        )
        evidence_score, evidence_query, evidence_result = evidence_payload
        score = max(score, evidence_score)
        query = evidence_query
        location_verified = homepage_matches_location(
            name,
            soup,
            verification_host,
            country,
            country_code,
            region,
            region_code,
            region_kind,
        )
        if not location_verified:
            location_verified = official_location_pages_match(
                soup,
                verification_url,
                verification_host,
                name,
                country,
                country_code,
                region,
                region_code,
                region_kind,
            )
        if not location_verified and regional_program_verified:
            location_verified = True
        if not location_verified:
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
            discovery_terms,
        ) // 3
        item = Institution(
            name=name,
            official_url=candidate_url,
            host=institution_host,
            source_query=query,
            score=score,
            evidence_url=evidence_result["url"],
        )
        return root, item, f"Accepted {name}: {candidate_url} (specialty evidence: {evidence_result['url']})"

    grouped_candidates = [
        (root, list(payloads.values()))
        for root, payloads in candidates_by_root.items()
        if payloads
    ]

    with ThreadPoolExecutor(max_workers=8) as executor:
        verified = executor.map(verify_candidate, grouped_candidates)
        for root, item, message in verified:
            log.append(message)
            if item is None:
                continue
            existing = institutions_by_root.get(root)
            if not existing or item.score > existing.score:
                institutions_by_root[root] = item

    institutions = deduplicate_institutions(institutions_by_root.values())
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
    declared_sitemaps: set[str] = set()
    robots_text = fetch_robots_txt(session, official_url)
    if robots_text:
        for line in robots_text.splitlines():
            if line.lower().startswith("sitemap:"):
                value = normalize_url(line.split(":", 1)[1].strip())
                if value:
                    declared_sitemaps.add(value)
    if declared_sitemaps:
        return sorted(declared_sitemaps)
    return [f"{root}/sitemap.xml", f"{root}/sitemap_index.xml"]


def common_department_paths(official_url: str, terms: list[str]) -> list[str]:
    root = url_root(official_url)
    if not root:
        return []
    slugs: set[str] = set()
    if terms:
        primary = terms[0]
        slugs.update({slugify(primary), re.sub(r"[^a-z0-9]+", "", primary.lower())})
    for term in terms[1:]:
        compact = re.sub(r"[^a-z0-9]+", "", term.lower())
        if compact and len(compact) <= 8:
            slugs.update({slugify(term), compact})
    slugs.discard("")
    prefixes = (
        "", "department", "departments", "school", "college", "medicine",
    )
    paths: set[str] = set()
    for slug in slugs:
        for prefix in prefixes:
            paths.add(f"{root}/{prefix}/{slug}" if prefix else f"{root}/{slug}")
            paths.add(f"{root}/{slug}/faculty")
            paths.add(f"{root}/{slug}/people")
    return sorted(paths)


def site_search_department_urls(
    host: str,
    region: str,
    specialty: str,
    terms: list[str],
    search_region: str = "wt-wt",
) -> list[dict[str, str]]:
    primary = terms[0] if terms else specialty
    short_alias = next(
        (
            term
            for term in terms[1:]
            if 3 <= len(re.sub(r"[^a-z0-9]+", "", term.lower())) <= 8
        ),
        primary,
    )
    email_domain = organization_root(host)
    queries = [
        f"site:{host} {primary} faculty",
        f"site:{host} {specialty} department faculty",
        f"site:{host} {primary} people directory",
        f"site:{host} {primary} academic staff",
        f"site:{host} {region} {primary} faculty",
        f'site:{host} "{short_alias}" faculty email',
        f'site:{host} orientation "{short_alias}" faculty',
        f'site:{host} onboarding "{short_alias}" faculty',
        f'site:{host} "@{email_domain}" "{short_alias}"',
    ]
    document_aliases = [alias for alias in ("ob/gyn", "ob-gyn") if alias in terms and alias != short_alias]
    for alias in document_aliases:
        queries.extend(
            [
                f'site:{host} orientation "{alias}" faculty',
                f'site:{host} "@{email_domain}" "{alias}"',
            ]
        )
    results: list[dict[str, str]] = []
    seen: set[str] = set()
    with ThreadPoolExecutor(max_workers=len(queries)) as executor:
        search_groups = list(executor.map(lambda query: ddg_search(query, search_region), queries))
    for query, search_results in zip(queries, search_groups):
        for item in search_results:
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
    country_code: str = "",
) -> tuple[list[PageCandidate], list[str], dict[str, str]]:
    session = make_session()
    official_host = institution.host
    candidates: dict[str, PageCandidate] = {}
    page_cache: dict[str, str] = {}
    log: list[str] = []
    verified_evidence_seed = False

    def shares_verified_program_scope(url: str) -> bool:
        evidence_url = normalize_url(institution.evidence_url)
        candidate_url = normalize_url(url)
        if not evidence_url or not candidate_url:
            return False
        evidence_host = host_of(evidence_url)
        candidate_host = host_of(candidate_url)
        if evidence_host != official_host and candidate_host == evidence_host:
            return True

        def program_tokens(value: str) -> set[str]:
            parts = [part for part in urlparse(value).path.lower().split("/") if part]
            tokens: set[str] = set()
            scope_markers = {"department", "departments", "program", "programs", "school", "schools"}
            for index, part in enumerate(parts[:-1]):
                if part in scope_markers:
                    token = re.sub(r"[^a-z0-9]+", "", parts[index + 1])
                    if len(token) >= 4:
                        tokens.add(token)
            return tokens

        return bool(program_tokens(evidence_url) & program_tokens(candidate_url))

    def add_candidate(url: str, title: str, source: str, page_text: str = "") -> None:
        normalized = normalize_url(url)
        if not normalized or not related_official_domain(normalized, official_host):
            return
        if not path_allowed(normalized, disallowed_paths):
            return
        path = urlparse(normalized).path.lower()
        query = urlparse(normalized).query.lower()
        is_pdf = is_pdf_url(normalized)
        if not is_pdf and (
            re.search(r"/(?:19|20)\d{2}(?:/|$)", path)
            or any(marker in path for marker in ("/category/", "/tag/", "/newsletter", "/news/", "/blog/"))
            or "attachment_id=" in query
        ):
            return
        if any(marker in path for marker in ("/person/", "/profile/")):
            return
        if "/person" in path and urlparse(normalized).query:
            return
        evidence = f"{normalized} {title} {page_text[:2500]}"
        if is_pdf:
            document_years = [int(year) for year in re.findall(r"\b(?:19|20)\d{2}\b", evidence)]
            if document_years and max(document_years) < time.gmtime().tm_year - 3:
                return
        matched = text_matches_terms(evidence, terms)
        page_identity = f"{path} {clean_text(title).lower()}"
        has_department_identity = any(word in page_identity for word in (*DEPARTMENT_PAGE_WORDS, *FACULTY_PAGE_WORDS))
        path_parts = {part for part in path.strip("/").split("/") if part}
        directory_paths = {
            "faculty", "faculty-staff", "faculty-and-staff", "faculty-directory",
            "people", "people-directory", "directory", "staff-directory",
        }
        directory_titles = (
            "faculty & staff", "faculty and staff", "faculty directory",
            "people directory", "staff directory", "our faculty",
        )
        strong_directory_seed = not is_pdf and (
            bool(path_parts & directory_paths)
            or any(phrase in clean_text(title).lower() for phrase in directory_titles)
        )
        trusted_pdf_seed = is_pdf and source in {"site_search", "document_hub"}
        if not matched and not strong_directory_seed and not trusted_pdf_seed:
            return
        primary_match = bool(terms and terms[0] in clean_text(evidence).lower())
        short_path_match = any(
            compact and len(compact) <= 10 and compact in re.sub(r"[^a-z0-9]+", "", normalized.lower())
            for compact in (re.sub(r"[^a-z0-9]+", "", term.lower()) for term in terms)
        )
        trusted_content_seed = (
            strong_directory_seed
            or trusted_pdf_seed
            or (source == "discovery_evidence" and bool(matched))
        )
        exact_specialty_title = bool(terms and terms[0] in clean_text(title).lower())
        if (
            source == "site_search"
            and verified_evidence_seed
            and not shares_verified_program_scope(normalized)
            and not exact_specialty_title
            and not short_path_match
        ):
            return
        if not primary_match and len(matched) < 2 and not short_path_match and not trusted_content_seed:
            return
        title_candidate = re.split(r"\s+[|\-:]\s+", clean_text(title))[0]
        if valid_name(title_candidate) and not has_department_identity:
            return
        if source not in {"homepage", "discovery_evidence"} and not is_pdf and not (
            strong_directory_seed or exact_specialty_title or short_path_match
        ):
            return
        score = relevance_score(normalized, title, page_text, terms)
        if strong_directory_seed:
            score = max(score, 25)
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

    if institution.evidence_url:
        evidence_html, evidence_final_url, _ = fetch_html(session, institution.evidence_url)
        if (
            evidence_html
            and evidence_final_url
            and related_official_domain(evidence_final_url, official_host)
        ):
            evidence_soup = BeautifulSoup(evidence_html, "html.parser")
            evidence_title = clean_text(
                evidence_soup.title.get_text(" ", strip=True) if evidence_soup.title else ""
            )
            evidence_text = clean_text(evidence_soup.get_text(" ", strip=True))
            page_cache[evidence_final_url] = evidence_html
            add_candidate(
                evidence_final_url,
                evidence_title,
                "discovery_evidence",
                evidence_text,
            )
            evidence_specialty_verified, _ = specialty_program_evidence(
                evidence_text,
                region,
                terms,
            )
            verified_evidence_seed = evidence_specialty_verified
            log.append("Verified institution-discovery evidence checked.")

            evidence_parts = [
                part for part in urlparse(evidence_final_url).path.split("/") if part
            ]
            scope_markers = {"department", "departments", "program", "programs", "school", "schools"}
            program_root = ""
            for index, part in enumerate(evidence_parts[:-1]):
                if part.lower() in scope_markers:
                    parsed_evidence = urlparse(evidence_final_url)
                    scoped_path = "/" + "/".join(evidence_parts[:index + 2])
                    program_root = f"{parsed_evidence.scheme}://{parsed_evidence.netloc}{scoped_path}"

            for anchor in evidence_soup.find_all("a", href=True):
                link = normalize_url(urljoin(evidence_final_url, anchor.get("href", "")))
                label = clean_text(anchor.get_text(" ", strip=True))
                combined = f"{link or ''} {label}".lower()
                if (
                    link
                    and shares_verified_program_scope(link)
                    and any(word in combined for word in (*DEPARTMENT_PAGE_WORDS, *FACULTY_PAGE_WORDS, "contact"))
                ):
                    add_candidate(link, label, "verified_evidence_link", label)

            if program_root:
                focused_paths = {
                    program_root,
                    f"{program_root}/faculty",
                    f"{program_root}/faculty-staff",
                    f"{program_root}/faculty-staff/index.cshtml",
                    f"{program_root}/faculty-and-staff",
                    f"{program_root}/people",
                    f"{program_root}/directory",
                    f"{program_root}/contact",
                    f"{program_root}/contact-us",
                }

                def probe_program_path(candidate_url: str) -> tuple[str, str | None, str | None]:
                    probe_session = make_session()
                    candidate_html, candidate_final_url, _ = fetch_html(probe_session, candidate_url)
                    return candidate_url, candidate_html, candidate_final_url

                with ThreadPoolExecutor(max_workers=len(focused_paths)) as executor:
                    focused_results = executor.map(probe_program_path, sorted(focused_paths))
                    for candidate_url, candidate_html, candidate_final_url in focused_results:
                        if not candidate_html or not candidate_final_url:
                            continue
                        candidate_soup = BeautifulSoup(candidate_html, "html.parser")
                        candidate_title = clean_text(
                            candidate_soup.title.get_text(" ", strip=True) if candidate_soup.title else ""
                        )
                        candidate_text = clean_text(candidate_soup.get_text(" ", strip=True))
                        page_cache[candidate_final_url] = candidate_html
                        add_candidate(
                            candidate_final_url,
                            candidate_title,
                            "verified_program_path",
                            candidate_text,
                        )
                log.append("Verified program pages checked.")

    scoped_program_pages = [
        item
        for item in candidates.values()
        if item.source in {"verified_evidence_link", "verified_program_path"}
    ]
    if verified_evidence_seed and scoped_program_pages:
        log.append("Verified program pages were sufficient; broad official-site search was unnecessary.")
        ordered = sorted(candidates.values(), key=lambda item: (-item.score, item.url))
        return ordered, log, page_cache

    for item in site_search_department_urls(
        official_host,
        region,
        specialty,
        terms,
        search_region_for_country(country_code),
    ):
        add_candidate(item["url"], item.get("title", ""), "site_search", item.get("body", ""))
    log.append("Official-site search checked.")

    if verified_evidence_seed:
        log.append("Verified evidence available; broad sitemap and guessed-path probing were unnecessary.")
        ordered = sorted(candidates.values(), key=lambda item: (-item.score, item.url))
        return ordered, log, page_cache

    sitemap_page_urls: set[str] = set()
    nested_sitemaps: set[str] = set()
    for sitemap in discover_sitemaps(session, institution.official_url):
        response, _, _ = fetch_response(session, sitemap)
        if not response:
            continue
        content = response.text
        if "xml" not in response.headers.get("Content-Type", "").lower() and "<url" not in content.lower():
            continue
        for found_url in extract_sitemap_urls(content):
            if found_url.lower().endswith(".xml"):
                nested_sitemaps.add(found_url)
            else:
                sitemap_page_urls.add(found_url)

    def fetch_nested_sitemap(sitemap_url: str) -> list[str]:
        nested_session = make_session()
        nested_response, _, _ = fetch_response(nested_session, sitemap_url)
        if not nested_response:
            return []
        return extract_sitemap_urls(nested_response.text)

    with ThreadPoolExecutor(max_workers=min(4, len(nested_sitemaps) or 1)) as executor:
        nested_results = executor.map(fetch_nested_sitemap, sorted(nested_sitemaps))
        for found_urls in nested_results:
            for found_url in found_urls:
                if found_url.lower().endswith(".xml"):
                    continue
                sitemap_page_urls.add(found_url)

    for sitemap_url in sorted(sitemap_page_urls):
        add_candidate(sitemap_url, "", "sitemap")
    log.append(f"Sitemap URLs checked: {len(sitemap_page_urls)}")

    root = url_root(institution.official_url)
    common_paths = set(common_department_paths(institution.official_url, terms))
    if root:
        common_paths.update(
            {
                f"{root}/faculty",
                f"{root}/faculty-staff",
                f"{root}/faculty-and-staff",
                f"{root}/people",
                f"{root}/directory",
                f"{root}/staff-directory",
                f"{root}/orientation",
                f"{root}/onboarding",
            }
        )

    def probe_common_path(candidate_url: str) -> tuple[str, str | None, str | None]:
        probe_session = make_session()
        html, final_candidate, _ = fetch_html(probe_session, candidate_url)
        return candidate_url, html, final_candidate

    with ThreadPoolExecutor(max_workers=min(4, len(common_paths) or 1)) as executor:
        common_results = list(executor.map(probe_common_path, sorted(common_paths)))
    for candidate_url, html, final_candidate in common_results:
        if not html or not final_candidate:
            continue
        if not related_official_domain(final_candidate, official_host):
            continue
        soup = BeautifulSoup(html, "html.parser")
        title = clean_text(soup.title.get_text(" ", strip=True) if soup.title else "")
        text = clean_text(soup.get_text(" ", strip=True))
        page_cache[final_candidate] = html
        add_candidate(final_candidate, title, "common_path", text)
        for anchor in soup.find_all("a", href=True):
            document_url = normalize_url(urljoin(final_candidate, anchor.get("href", "")))
            if document_url and is_pdf_url(document_url):
                add_candidate(
                    document_url,
                    clean_text(anchor.get_text(" ", strip=True)),
                    "document_hub",
                )
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


def should_follow_faculty_link(
    source_url: str,
    target_url: str,
    link_text: str,
    source_has_department_terms: bool,
    terms: list[str],
) -> bool:
    combined = f"{target_url} {link_text}".lower()
    if text_matches_terms(combined, terms):
        return True
    if looks_like_profile_url(target_url, link_text):
        return False
    if not source_has_department_terms or not any(word in combined for word in FACULTY_PAGE_WORDS):
        return False
    source_parts = {part for part in urlparse(source_url).path.lower().split("/") if len(part) >= 4}
    target_parts = {part for part in urlparse(target_url).path.lower().split("/") if len(part) >= 4}
    generic_parts = {"about", "academics", "department", "departments", "faculty", "people", "staff", "medicine"}
    return bool((source_parts - generic_parts) & (target_parts - generic_parts))


def page_is_department_scoped(page_url: str, title: str, terms: list[str]) -> bool:
    header = clean_text(f"{page_url} {title}").lower()
    if terms and terms[0] in header:
        return True
    compact_url = re.sub(r"[^a-z0-9]+", "", page_url.lower())
    return any(
        compact and len(compact) <= 10 and compact in compact_url
        for compact in (re.sub(r"[^a-z0-9]+", "", term.lower()) for term in terms)
    )


PROFILE_HINTS = (
    "/profile", "/profiles", "/people", "/person", "/faculty", "/staff",
    "/directory", "/bio", "/biography",
)


def looks_like_profile_url(url: str, link_text: str = "") -> bool:
    lowered_url = url.lower()
    lowered_text = clean_text(link_text).lower()
    combined = f"{lowered_url} {lowered_text}"
    if not any(hint in lowered_url for hint in PROFILE_HINTS) and not any(
        word in lowered_text for word in ("profile", "biography", "bio", "view faculty")
    ):
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
    "MSPH", "MSCR", "MSCI", "DHA", "CMPE",
    "MLIS", "FACOI", "FACOFP", "FACEP", "FAAEM", "FACOOG", "MSCP", "FNPC",
}

NAME_SUFFIXES = {"JR", "SR", "II", "III", "IV", "V"}

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
    "utility", "navigation", "helpful", "links", "annual", "report",
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
    r"\bclerkship\s+director\b",
    r"\bsupervising\s+physician\b",
    r"\bclinical\s+preceptor\b",
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
    (r"\bfellowship\s+(?:trainee|position|appointment)\b", "Fellowship role"),
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
    comma_parts = [part.strip() for part in value.split(",") if part.strip()]
    if len(comma_parts) >= 2 and len(comma_parts[0].split()) == 1:
        suffix = ""
        if compact_local(comma_parts[-1]).upper() in NAME_SUFFIXES:
            suffix = f", {comma_parts.pop()}"
        if len(comma_parts) == 2:
            value = f"{comma_parts[1]} {comma_parts[0]}{suffix}"
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
    value = value.replace(".", "")
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
            if (
                len(roster_parts) >= 2
                and parts[-1] == roster_parts[-1]
                and parts[0][:1] == roster_parts[0][:1]
                and (len(parts[0]) == 1 or len(roster_parts[0]) == 1)
            ):
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


def decode_protected_script_emails(node: BeautifulSoup | Tag) -> set[str]:
    emails: set[str] = set()
    for script in node.find_all("script"):
        source = script.string or script.get_text(" ", strip=True)
        if not source or "decodeURIComponent" not in source:
            continue

        for match in re.finditer(r"decodeURIComponent\(\s*(['\"])(.*?)\1\s*\)", source, flags=re.S):
            encoded = match.group(2)
            if encoded != "o":
                emails.update(decode_visible_emails(unquote(encoded)))

        alphabet_match = re.search(r"var\s+ml\s*=\s*(['\"])(.*?)\1", source, flags=re.S)
        indexes_match = re.search(r"\bmi\s*=\s*(['\"])(.*?)\1", source, flags=re.S)
        if alphabet_match and indexes_match:
            alphabet = alphabet_match.group(2)
            indexes = indexes_match.group(2)
            decoded = "".join(
                alphabet[index]
                for character in indexes
                if 0 <= (index := ord(character) - 48) < len(alphabet)
            )
            emails.update(decode_visible_emails(unquote(decoded)))
    return emails


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
    if node.name == "tr":
        cells = node.find_all(["td", "th"], recursive=False)
        if len(cells) >= 2:
            surname = clean_text(cells[0].get_text(" ", strip=True))
            given_names = clean_text(cells[1].get_text(" ", strip=True))
            candidate = clean_name(f"{given_names} {surname}")
            if valid_name(candidate):
                return candidate
    return None


def collect_names_in_node(node: Tag, limit: int = 6) -> set[str]:
    names: set[str] = set()
    node_name = extract_name_from_node(node)
    if node_name:
        names.add(normalize_person_name(node_name))
    for selector in (*NAME_SELECTORS, "a[href]"):
        for child in node.select(selector):
            candidate = clean_name(child.get_text(" ", strip=True))
            if valid_name(candidate):
                names.add(normalize_person_name(candidate))
                if len(names) > limit:
                    return names
    return names


def extract_title_text(node: Tag, full_text: str, name: str | None) -> str:
    fallback = None
    for selector in TITLE_SELECTORS:
        for element in node.select(selector):
            value = clean_text(element.get_text(" ", strip=True))
            if 3 <= len(value) <= 220:
                fallback = fallback or value
                if matched_allowed_title(value) or excluded_role_reason(value):
                    return value
    if fallback:
        return fallback
    if name:
        index = full_text.find(name)
        if index != -1:
            return full_text[index + len(name):index + len(name) + 220]
    return full_text[:220]


def page_has_js_only_signals(soup: BeautifulSoup, text: str) -> bool:
    scripts = soup.find_all("script")
    app_roots = soup.select("#root, #app, [data-reactroot], [id*='__next']")
    return len(text) < 250 and (len(scripts) >= 4 or bool(app_roots))


def faculty_candidate_nodes(soup: BeautifulSoup) -> list[Tag]:
    nodes: list[Tag] = list(soup.select(CANDIDATE_NODE_SELECTOR))
    seen = {id(node) for node in nodes}
    for heading in soup.find_all(["h2", "h3", "h4", "h5"]):
        name = clean_name(heading.get_text(" ", strip=True))
        if not valid_name(name):
            continue
        current: Tag = heading
        for _ in range(5):
            parent = current.parent
            if not isinstance(parent, Tag):
                break
            current = parent
            text = clean_text(current.get_text(" ", strip=True))
            if not 10 <= len(text) <= 2000:
                continue
            title_text = extract_title_text(current, text, name)
            if matched_allowed_title(title_text) or excluded_role_reason(title_text):
                if id(current) not in seen:
                    seen.add(id(current))
                    nodes.append(current)
                break
    return nodes


def extract_roster_entries_from_soup(page_url: str, soup: BeautifulSoup) -> tuple[list[FacultyEntry], list[Rejection]]:
    entries: list[FacultyEntry] = []
    rejections: list[Rejection] = []
    entries_by_name: dict[str, FacultyEntry] = {}

    for node in faculty_candidate_nodes(soup):
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
        profile_url = None
        for anchor in node.find_all("a", href=True):
            target = normalize_url(urljoin(page_url, anchor.get("href", "")))
            if target and looks_like_profile_url(target, anchor.get_text(" ", strip=True)):
                profile_url = target
                break
        existing = entries_by_name.get(normalized)
        if existing:
            if not existing.profile_url and profile_url:
                existing.profile_url = profile_url
            continue
        entry = FacultyEntry(
            name=name,
            normalized_name=normalized,
            title=allowed.title(),
            source_url=page_url,
            evidence=text[:2000],
            profile_url=profile_url,
        )
        entries.append(entry)
        entries_by_name[normalized] = entry
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
            department_scoped = page_is_department_scoped(final_url, title, terms)
            for entry in found_entries:
                if department_scoped or text_matches_terms(entry.evidence, terms):
                    roster.setdefault(entry.normalized_name, entry)
                else:
                    rejections.append(
                        Rejection(entry.name, "Outside requested department", final_url, entry.title)
                    )
            rejections.extend(found_rejections)

        is_faculty_listing = any(word in combined_header for word in FACULTY_PAGE_WORDS)
        if is_faculty_listing:
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
            if should_follow_faculty_link(
                final_url,
                link,
                link_text,
                bool(text_matches_terms(f"{final_url} {title} {page_text}", terms)),
                terms,
            ):
                queue.append(link)

        log.append(f"[{len(visited)} checked] {final_url}")
        if delay_seconds > 0:
            time.sleep(delay_seconds)

    return list(roster.values()), sorted(set(faculty_pages)), rejections, page_cache, log, blocked


def filter_roster_to_location(
    roster_entries: list[FacultyEntry],
    country_code: str,
    region: str,
    region_code: str,
    region_kind: str,
) -> list[FacultyEntry]:
    if not region:
        return roster_entries
    aliases = location_scope_aliases(country_code, region, region_code, region_kind)
    if not aliases:
        return roster_entries

    labeled: list[FacultyEntry] = []
    matching: set[str] = set()
    for entry in roster_entries:
        if not re.search(r"\b(?:campus|location)\s*:", entry.evidence, flags=re.I):
            continue
        labeled.append(entry)
        folded_evidence = fold_text(entry.evidence)
        if any(
            re.search(
                rf"\b(?:campus|location)\s*:\s*[^:]{{0,80}}\b{re.escape(fold_text(alias))}\b",
                folded_evidence,
            )
            for alias in aliases
        ):
            matching.add(entry.normalized_name)

    if len(labeled) < 2 or not matching:
        return roster_entries
    labeled_names = {entry.normalized_name for entry in labeled}
    return [
        entry
        for entry in roster_entries
        if entry.normalized_name not in labeled_names or entry.normalized_name in matching
    ]


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
            else:
                continue
            item = {"url": target, "text": text, "score": score, "from": page_url}
            if target not in links or score > int(links[target]["score"]):
                links[target] = item
    for entry in roster_entries:
        if entry.profile_url and entry.profile_url not in links:
            links[entry.profile_url] = {"url": entry.profile_url, "text": entry.name, "score": 90, "from": entry.source_url}
    by_identity: dict[str, dict[str, object]] = {}
    for item in links.values():
        url = str(item["url"])
        parsed = urlparse(url)
        query = parse_qs(parsed.query)
        identifier = next(
            (values[0] for key in ("id", "uid", "person_id", "profile_id") if (values := query.get(key))),
            "",
        )
        identity = f"{organization_root(parsed.hostname or '')}:{identifier}" if identifier else url
        existing = by_identity.get(identity)
        if not existing or int(item["score"]) > int(existing["score"]):
            by_identity[identity] = item
    return sorted(by_identity.values(), key=lambda item: (-int(item["score"]), str(item["url"])))


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


def looks_institutional_email_domain(domain: str) -> bool:
    domain = domain.lower().removeprefix("www.")
    if is_academic_domain(domain):
        return True
    if domain.endswith(".gov") or re.search(r"\.gov\.[a-z]{2}$", domain):
        return True
    return any(
        marker in domain
        for marker in ("university", "college", "hospital", "health", "medical", "medicine", "clinic")
    )


def looks_affiliated_institutional_domain(domain: str, official_host: str) -> bool:
    if not looks_institutional_email_domain(domain):
        return False
    domain_label = organization_root(domain).split(".", 1)[0]
    official_label = organization_root(official_host).split(".", 1)[0]
    generic = {"university", "college", "hospital", "health", "medical", "medicine", "clinic", "center", "centre"}
    domain_tokens = {token for token in re.split(r"[^a-z0-9]+", domain_label) if token and token not in generic}
    official_tokens = {token for token in re.split(r"[^a-z0-9]+", official_label) if token and token not in generic}
    return any(
        len(left) >= 3 and len(right) >= 3 and (left in right or right in left)
        for left in domain_tokens
        for right in official_tokens
    )


def classify_email(
    email: str,
    official_host: str,
    allow_published_affiliate: bool = False,
) -> tuple[bool, str | None]:
    email = trim_run_on_email(email)
    if not EMAIL_RE.fullmatch(email):
        return False, "Malformed email"
    local, domain = email.split("@", 1)
    local_compact = compact_local(local)
    if domain in PERSONAL_EMAIL_DOMAINS:
        return False, "Personal email domain"
    if local_compact in GENERIC_EMAIL_PREFIXES:
        return False, "Generic email"
    if (
        not email_domain_belongs(domain, official_host)
        and not looks_affiliated_institutional_domain(domain, official_host)
        and not allow_published_affiliate
    ):
        return False, "Outside official domain family"
    return True, None


def is_verified_evidence_page(source_url: str, institution: Institution) -> bool:
    source = normalize_url(source_url)
    evidence = normalize_url(institution.evidence_url)
    return bool(source and evidence and source.rstrip("/") == evidence.rstrip("/"))


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
    emails.update(decode_protected_script_emails(block))
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

    for element in soup.select("[data-enc-email], a.mail-link"):
        context = ancestor_context(element)
        for email in decode_visible_emails(element.get_text(" ", strip=True)):
            add(email, context, "protected_attribute", context)

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

    for email in decode_protected_script_emails(soup):
        add(email, page_text[:700], "protected_script", page_text[:700])

    return occurrences


def is_displayed_contact(entries: list[dict[str, str]]) -> bool:
    for entry in entries:
        if entry["source"] in {"mailto", "protected_attribute", "protected_script"}:
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

def is_generic_department_local(
    local: str,
    terms: list[str],
    source_url: str = "",
    context: str = "",
) -> bool:
    compact = compact_local(local)
    if compact in GENERIC_EMAIL_PREFIXES or compact in DEPARTMENT_MAILBOX_WORDS:
        return True
    term_tokens = {compact_local(term) for term in terms if len(compact_local(term)) >= 4}
    if any(token == compact or token in compact for token in term_tokens):
        return True

    path_tokens = {
        re.sub(r"[^a-z0-9]+", "", part.lower())
        for part in urlparse(source_url).path.split("/")
        if len(re.sub(r"[^a-z0-9]+", "", part.lower())) >= 4
    }
    mailbox_parts = {
        re.sub(r"[^a-z0-9]+", "", part.lower())
        for part in re.split(r"[._-]+", local)
        if len(re.sub(r"[^a-z0-9]+", "", part.lower())) >= 4
    }
    contact_labeled = bool(re.search(r"\b(?:contact us|department contact|program contact)\b", context, flags=re.I))
    return contact_labeled and bool(path_tokens & mailbox_parts)


def find_generic_department_email(
    department_pages: list[PageCandidate],
    institution: Institution,
    terms: list[str],
    page_cache: dict[str, str],
) -> Contact | None:
    session = make_session()
    candidates: list[tuple[int, str, str]] = []
    for page in department_pages:
        html = page_cache.get(page.url)
        final_url = page.url
        if html is None:
            html, final_url, _ = fetch_html(session, page.url)
        if not html or not final_url:
            continue
        soup = BeautifulSoup(html, "html.parser")
        for tag in soup(["nav", "script", "style", "noscript"]):
            tag.decompose()
        text = clean_text(soup.get_text(" ", strip=True))
        if not text_matches_terms(f"{final_url} {text}", terms):
            continue
        occurrences = extract_emails_with_context(soup, text)
        for email, entries in occurrences.items():
            if "@" not in email:
                continue
            local, domain = email.split("@", 1)
            context = " ".join(entry.get("context", "") for entry in entries)
            if not email_domain_belongs(domain, institution.host):
                continue
            if not is_generic_department_local(local, terms, final_url, context):
                continue
            score = 100
            if compact_local(local) in {compact_local(term) for term in terms}:
                score += 30
            if re.search(r"\b(?:contact us|department contact|program contact)\b", context, flags=re.I):
                score += 20
            if page.source == "discovery_evidence":
                score += 10
            candidates.append((score, email, final_url))

    if not candidates:
        return None
    _, email, source_url = sorted(candidates, key=lambda item: (-item[0], item[1]))[0]
    return Contact(
        name="Department Contact",
        email=email,
        institution=institution.name,
        source_url=source_url,
        method="Generic department fallback",
        strength=9,
    )


def fallback_email_score(email: str, context: str, source_url: str, terms: list[str]) -> tuple[int, str]:
    if "@" not in email:
        return -1, "Institution Contact"
    local, _ = email.split("@", 1)
    compact = compact_local(local)
    folded_context = fold_text(f"{context} {source_url}")
    score = 0
    label = "Institution Contact"

    department_terms = [compact_local(term) for term in terms if compact_local(term)]
    if compact in department_terms or any(term in compact for term in department_terms if len(term) >= 5):
        score = 140
        label = "Department Contact"

    priorities = (
        (("facultyaffairs", "faculty affairs"), 130, "Faculty Affairs Contact"),
        (("academicaffairs", "academic affairs"), 125, "Academic Affairs Contact"),
        (("medicaleducation", "medical education"), 120, "Medical Education Contact"),
        (("continuingmedicaleducation", "continuing medical education", "cme"), 115, "Medical Education Contact"),
        (("conference", "conferences", "events", "event"), 105, "Events Contact"),
        (("outreach", "externalrelations", "external relations", "communityrelations"), 95, "Outreach Contact"),
        (("communications", "communication"), 85, "Communications Contact"),
    )
    for needles, value, candidate_label in priorities:
        if any(needle in compact or needle in folded_context for needle in needles):
            if value > score:
                score = value
                label = candidate_label

    generic_scores = {
        "info": 60,
        "contact": 60,
        "generalinfo": 58,
        "office": 55,
        "enquiries": 55,
        "inquiries": 55,
        "hello": 50,
        "reception": 45,
    }
    score = max(score, generic_scores.get(compact, 0))
    if compact in {"admissions", "webmaster", "support", "billing", "privacy", "careers", "hr"}:
        score -= 80
    return score, label


def find_institution_conference_contact(
    institution: Institution,
    terms: list[str],
    disallowed_paths: list[str],
) -> Contact | None:
    root = url_root(institution.official_url)
    if not root:
        return None
    page_hints = (
        "contact", "faculty affairs", "academic affairs", "medical education",
        "continuing medical education", "cme", "event", "conference",
        "outreach", "external relations", "communications",
    )
    urls = {
        institution.official_url,
        f"{root}/contact",
        f"{root}/contact-us",
        f"{root}/faculty-affairs",
        f"{root}/academic-affairs",
        f"{root}/medical-education",
        f"{root}/continuing-medical-education",
        f"{root}/cme",
        f"{root}/events",
        f"{root}/outreach",
        f"{root}/communications",
    }

    homepage_session = make_session()
    homepage_html, homepage_url, _ = fetch_html(homepage_session, institution.official_url)
    allowed_hosts = {institution.host}
    if homepage_url:
        allowed_hosts.add(host_of(homepage_url))

    def institution_page_allowed(url: str) -> bool:
        return any(related_official_domain(url, allowed_host) for allowed_host in allowed_hosts)

    if homepage_html and homepage_url:
        homepage_soup = BeautifulSoup(homepage_html, "html.parser")
        for anchor in homepage_soup.find_all("a", href=True):
            link = normalize_url(urljoin(homepage_url, anchor.get("href", "")))
            label = clean_text(anchor.get_text(" ", strip=True)).casefold()
            combined = f"{link or ''} {label}".casefold()
            if (
                link
                and institution_page_allowed(link)
                and path_allowed(link, disallowed_paths)
                and any(hint in combined for hint in page_hints)
            ):
                urls.add(link)

    urls = {
        url
        for url in urls
        if institution_page_allowed(url) and path_allowed(url, disallowed_paths)
    }

    def read_contact_page(url: str) -> tuple[str, str | None]:
        page_session = make_session()
        html, final_url, _ = fetch_html(page_session, url)
        if not html or not final_url or not institution_page_allowed(final_url):
            return url, None
        return final_url, html

    candidates: list[tuple[int, str, str, str]] = []
    with ThreadPoolExecutor(max_workers=min(4, len(urls) or 1)) as executor:
        for page_url, html in executor.map(read_contact_page, sorted(urls)):
            if not html:
                continue
            soup = BeautifulSoup(html, "html.parser")
            page_text = clean_text(soup.get_text(" ", strip=True))
            occurrences = extract_emails_with_context(soup, page_text)
            for email, entries in occurrences.items():
                if "@" not in email or not is_displayed_contact(entries):
                    continue
                _, domain = email.split("@", 1)
                if domain in PERSONAL_EMAIL_DOMAINS:
                    continue
                if not any(
                    email_domain_belongs(domain, allowed_host)
                    or looks_affiliated_institutional_domain(domain, allowed_host)
                    for allowed_host in allowed_hosts
                ):
                    continue
                context = " ".join(entry.get("context", "") for entry in entries)
                score, label = fallback_email_score(email, context, page_url, terms)
                if score > 0:
                    candidates.append((score, label, email, page_url))

    if not candidates:
        return None
    score, label, email, source_url = sorted(
        candidates,
        key=lambda item: (-item[0], item[2].casefold(), item[3]),
    )[0]
    return Contact(
        name=label,
        email=email,
        institution=institution.name,
        source_url=source_url,
        method="Institution conference contact fallback",
        strength=10,
    )


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
    protected_emails = decode_protected_script_emails(soup)
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
    for email in protected_emails:
        contexts.setdefault(email, []).append({
            "context": page_text[:700],
            "source": "protected_script",
            "before": page_text[:700],
        })
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


def fetch_public_profile_payload(
    session: requests.Session,
    profile_url: str,
    html: str,
) -> tuple[dict[str, object] | None, str | None]:
    if "/javascript/configuration.js" not in html:
        return None, None
    match = re.match(r"^/(\d+)(?:-|$)", urlparse(profile_url).path)
    root = url_root(profile_url)
    if not match or not root:
        return None, None
    api_url = f"{root}/api/users/{match.group(1)}"
    response, _, error = fetch_response(session, api_url)
    if not response:
        return None, error or "Public profile API unavailable"
    try:
        payload = response.json()
    except ValueError:
        return None, "Public profile API returned invalid JSON"
    if not isinstance(payload, dict):
        return None, "Public profile API returned an unexpected record"
    return payload, None


def parse_public_profile_payload(
    profile_url: str,
    payload: dict[str, object],
    institution: Institution,
    roster_entries: list[FacultyEntry],
) -> tuple[list[Contact], list[Rejection]]:
    first_name = clean_text(payload.get("firstName"))
    last_name = clean_text(payload.get("lastName"))
    name = clean_name(clean_text(payload.get("firstNameLastName")) or f"{first_name} {last_name}")
    roster_names = {entry.normalized_name for entry in roster_entries}
    if not valid_name(name) or not roster_name_match(name, roster_names):
        return [], [Rejection(name or "Unknown profile", "Not on approved roster", profile_url)]

    matched_entry = next(
        (entry for entry in roster_entries if roster_name_match(name, {entry.normalized_name})),
        None,
    )
    display_name = matched_entry.name if matched_entry else name
    raw_emails: set[str] = set()
    primary = payload.get("emailAddress")
    if isinstance(primary, dict):
        raw_emails.update(decode_visible_emails(clean_text(primary.get("address"))))
    alternatives = payload.get("otherEmailAddresses")
    if isinstance(alternatives, list):
        for item in alternatives:
            if isinstance(item, dict):
                raw_emails.update(decode_visible_emails(clean_text(item.get("address"))))

    contacts: list[Contact] = []
    rejections: list[Rejection] = []
    for email in sorted(raw_emails):
        ok, reason = classify_email(email, institution.host)
        if ok:
            contacts.append(Contact(display_name, email, institution.name, profile_url, "Official public profile API", 0))
        elif reason:
            rejections.append(Rejection(display_name, reason, profile_url, email))
    if not contacts:
        rejections.append(Rejection(display_name, "No visible institutional email", profile_url))
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
        if not found_contacts:
            payload, payload_error = fetch_public_profile_payload(session, final_url, html)
            if payload:
                api_contacts, api_rejections = parse_public_profile_payload(
                    final_url,
                    payload,
                    institution,
                    roster_entries,
                )
                found_contacts.extend(api_contacts)
                found_rejections.extend(api_rejections)
            elif payload_error:
                blocked.append(f"{final_url}: {payload_error}")
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
    wanted = {entry.normalized_name: entry for entry in pending}
    matched: set[str] = set()

    for page_url, html in page_cache.items():
        soup = BeautifulSoup(html, "html.parser")
        for node in faculty_candidate_nodes(soup):
            node_name = extract_name_from_node(node)
            if not node_name:
                continue
            normalized = normalize_person_name(node_name)
            entry = wanted.get(normalized)
            if not entry:
                possible_entries = [
                    candidate
                    for candidate in pending
                    if roster_name_match(node_name, {candidate.normalized_name})
                ]
                if len(possible_entries) == 1:
                    entry = possible_entries[0]
                    normalized = entry.normalized_name
            if not entry or normalized in matched:
                continue
            block_text = clean_text(node.get_text(" ", strip=True))
            if is_admin_context(block_text):
                continue
            if len(collect_names_in_node(node)) != 1 and node.name not in {"article", "tr"}:
                continue
            emails = emails_in_local_block(node, block_text)
            valid_found = False
            for email in sorted(emails):
                ok, reason = classify_email(
                    email,
                    institution.host,
                    allow_published_affiliate=is_verified_evidence_page(page_url, institution),
                )
                if ok:
                    valid_found = True
                    contacts.append(Contact(entry.name, email, institution.name, page_url, "Faculty directory card", 1))
                elif reason:
                    rejections.append(Rejection(entry.name, reason, page_url, email))
            if not valid_found:
                rejections.append(Rejection(entry.name, "No visible institutional email", page_url))
            else:
                matched.add(normalized)
    for entry in pending:
        if entry.normalized_name not in matched:
            rejections.append(Rejection(entry.name, "No precise local card match", entry.source_url))
    return contacts, rejections


def extract_pdf_contacts(
    department_pages: list[PageCandidate],
    institution: Institution,
    terms: list[str],
) -> tuple[list[Contact], list[Rejection]]:
    contacts: list[Contact] = []
    rejections: list[Rejection] = []
    pdf_pages = [page for page in department_pages if is_pdf_url(page.url)]

    def fetch_document(page: PageCandidate) -> tuple[PageCandidate, str | None, str | None]:
        document_session = make_session()
        text, error = fetch_pdf_text(document_session, page.url)
        return page, text, error

    with ThreadPoolExecutor(max_workers=min(4, len(pdf_pages) or 1)) as executor:
        documents = executor.map(fetch_document, pdf_pages)
        for page, text, error in documents:
            if error or not text or not text_matches_terms(text, terms):
                continue
            lines = [clean_text(line) for line in text.splitlines() if clean_text(line)]
            for index, line in enumerate(lines):
                emails = decode_visible_emails(line)
                if not emails:
                    continue
                name = None
                name_index = None
                for candidate_index in range(index, max(-1, index - 9), -1):
                    candidate_line = lines[candidate_index]
                    if "@" in candidate_line or ":" in candidate_line:
                        continue
                    candidate = clean_name(candidate_line)
                    if valid_name(candidate):
                        name = candidate
                        name_index = candidate_index
                        break
                if not name or name_index is None:
                    continue
                context = clean_text(" ".join(lines[name_index:index + 1]))
                if len(context) > 900:
                    continue
                if not text_matches_terms(context, terms):
                    continue
                reason = excluded_role_reason(context)
                allowed = matched_allowed_title(context)
                if reason or not allowed:
                    rejections.append(Rejection(name, reason or "No current faculty title", page.url, context[:180]))
                    continue
                if is_admin_context(context):
                    rejections.append(Rejection(name, "Administrative context", page.url, context[:180]))
                    continue
                for email in emails:
                    ok, email_reason = classify_email(
                        email,
                        institution.host,
                        allow_published_affiliate=is_verified_evidence_page(page.url, institution),
                    )
                    if ok:
                        contacts.append(Contact(name, email, institution.name, page.url, "Official PDF", 2))
                    elif email_reason:
                        rejections.append(Rejection(name, email_reason, page.url, email))
    return contacts, rejections


def extract_verified_evidence_contacts(
    institution: Institution,
    terms: list[str],
    region: str,
) -> tuple[list[Contact], list[Rejection], bool]:
    evidence_url = normalize_url(institution.evidence_url)
    if not evidence_url or not related_official_domain(evidence_url, institution.host):
        return [], [], False

    html, final_url, _ = fetch_html(make_session(), evidence_url)
    if not html or not final_url or not related_official_domain(final_url, institution.host):
        return [], [], False

    soup = BeautifulSoup(html, "html.parser")
    page_text = clean_text(soup.get_text(" ", strip=True))
    folded_page = fold_text(page_text)
    teaching_markers = (
        "clinical faculty", "teaching faculty", "clerkship", "clinical rotation",
        "medical students", "supervising physician", "preceptor",
    )
    specialty_verified, regional_program_verified = specialty_program_evidence(
        page_text,
        region,
        terms,
    )
    if not specialty_verified or not any(
        marker in folded_page for marker in teaching_markers
    ):
        return [], [], regional_program_verified

    contacts: list[Contact] = []
    rejections: list[Rejection] = []
    seen_pairs: set[tuple[str, str]] = set()
    credential_re = re.compile(
        r"\b(?:M\.?D\.?|D\.?O\.?|Ph\.?D\.?|MBBS|MBChB|FACOG)\b",
        flags=re.I,
    )

    for anchor in soup.select('a[href^="mailto:" i]'):
        address = anchor.get("href", "")[7:].split("?", 1)[0]
        emails = sorted(decode_visible_emails(f"{address} {anchor.get_text(' ', strip=True)}"))
        if not emails:
            continue

        block: Tag = anchor
        block_name = None
        block_text = ""
        for _ in range(5):
            parent = block.parent
            if not isinstance(parent, Tag):
                break
            block = parent
            candidate_text = clean_text(block.get_text(" ", strip=True))
            if not 8 <= len(candidate_text) <= 900:
                continue
            candidate_name = extract_name_from_node(block)
            if candidate_name and credential_re.search(candidate_text):
                block_name = candidate_name
                block_text = candidate_text
                break
        if not block_name or is_admin_context(block_text):
            continue

        for email in emails:
            ok, reason = classify_email(
                email,
                institution.host,
                allow_published_affiliate=True,
            )
            pair = (normalize_person_name(block_name), email)
            if ok and pair not in seen_pairs:
                seen_pairs.add(pair)
                contacts.append(
                    Contact(
                        clean_name(block_name),
                        email,
                        institution.name,
                        final_url,
                        "Verified official teaching evidence",
                        0,
                    )
                )
            elif reason:
                rejections.append(Rejection(block_name, reason, final_url, email))

    return deduplicate_contacts(contacts), rejections, regional_program_verified


def process_institution(
    institution: Institution,
    country: str,
    region: str,
    specialty: str,
    custom_keywords: str,
    delay_seconds: float,
    country_code: str = "",
    region_code: str = "",
    region_kind: str = "Region",
    progress_callback: Callable[[str], None] | None = None,
) -> tuple[list[Contact], InstitutionReport]:
    def update_activity(message: str) -> None:
        if progress_callback:
            progress_callback(message)

    terms = resolve_terms(specialty, custom_keywords)
    session = make_session()
    report = InstitutionReport(institution=institution.name, status="Manual review required", official_url=institution.official_url)

    update_activity("🌐 Opening official website...")
    robots_text = fetch_robots_txt(session, institution.official_url)
    disallowed_paths = parse_disallowed_paths(robots_text or "")
    if robots_text:
        report.notes.append("robots.txt checked")

    update_activity("🔎 Reviewing verified official evidence...")
    evidence_contacts, evidence_rejections, evidence_is_regional_program = extract_verified_evidence_contacts(
        institution,
        terms,
        region,
    )
    report.rejections.extend(evidence_rejections)
    if evidence_contacts:
        report.notes.append(
            f"Verified discovery evidence yielded {len(evidence_contacts)} faculty contact(s)."
        )
    if evidence_contacts and evidence_is_regional_program:
        report.department_pages = 1
        report.faculty_roster_entries = len(evidence_contacts)
        report.pages_checked = 1
        report.contacts_found = len(evidence_contacts)
        report.status = "Verified contacts found"
        report.notes.append("Region-specific teaching page used as the authoritative contact source.")
        update_activity(f"✨ Finishing {institution.name}...")
        return evidence_contacts, report

    def best_published_fallback(
        department_pages: list[PageCandidate],
        page_cache: dict[str, str],
    ) -> tuple[list[Contact], InstitutionReport] | None:
        update_activity("📨 Finding the best published contact...")
        department_contact = find_generic_department_email(
            department_pages,
            institution,
            terms,
            page_cache,
        )
        if department_contact:
            report.contacts_found = 1
            report.status = "Generic department contact found"
            report.notes.append("No personal faculty emails were verified; one department contact returned.")
            return [department_contact], report
        institution_contact = find_institution_conference_contact(
            institution,
            terms,
            disallowed_paths,
        )
        if institution_contact:
            report.contacts_found = 1
            report.status = "Institution conference contact found"
            report.notes.append(
                "No personal faculty or department email was verified; the best published institutional contact returned."
            )
            return [institution_contact], report
        return None

    update_activity("🔎 Discovering relevant pages...")
    department_pages, department_log, seed_cache = discover_department_pages(
        institution=institution,
        region=region,
        specialty=specialty,
        terms=terms,
        disallowed_paths=disallowed_paths,
        country_code=country_code,
    )
    report.department_pages = len(department_pages)
    report.notes.extend(department_log[:5])
    if not department_pages:
        update_activity(f"✨ Finishing {institution.name}...")
        if evidence_contacts:
            report.contacts_found = len(evidence_contacts)
            report.status = "Verified contacts found"
            return evidence_contacts, report
        fallback_result = best_published_fallback([], seed_cache)
        if fallback_result:
            return fallback_result
        report.status = "Relevant department not found"
        return [], report

    update_activity("📄 Reviewing discovered pages...")
    roster_entries, faculty_pages, role_rejections, page_cache, crawl_log, blocked = discover_faculty_roster(
        department_pages=department_pages,
        institution=institution,
        terms=terms,
        delay_seconds=delay_seconds,
        disallowed_paths=disallowed_paths,
        seed_cache=seed_cache,
    )
    unfiltered_roster_count = len(roster_entries)
    roster_entries = filter_roster_to_location(
        roster_entries,
        country_code,
        region,
        region_code,
        region_kind,
    )
    if len(roster_entries) != unfiltered_roster_count:
        report.notes.append(
            f"Location-labeled roster filtered from {unfiltered_roster_count} to {len(roster_entries)} entries."
        )
    report.faculty_roster_entries = len(roster_entries)
    report.pages_checked = len(crawl_log)
    report.blocked_or_unreadable.extend(blocked)
    report.rejections.extend(role_rejections)
    report.notes.extend(crawl_log[:8])

    update_activity("📄 Reviewing official documents...")
    pdf_contacts, pdf_rejections = extract_pdf_contacts(department_pages, institution, terms)
    report.rejections.extend(pdf_rejections)

    if not roster_entries:
        update_activity(f"✨ Finishing {institution.name}...")
        verified_contacts = deduplicate_contacts(evidence_contacts + pdf_contacts)
        if verified_contacts:
            report.contacts_found = len(verified_contacts)
            report.status = "Verified contacts found"
            return verified_contacts, report
        fallback_result = best_published_fallback(department_pages, page_cache)
        if fallback_result:
            return fallback_result
        if any("JavaScript-only" in line for line in crawl_log):
            report.status = "JavaScript-only directory"
        elif blocked and not crawl_log:
            report.status = "Website blocked automated access"
        else:
            report.status = "Faculty page not found"
        return [], report

    update_activity("🧭 Following relevant faculty links...")
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

    update_activity("✉️ Verifying published institutional emails...")
    covered_names = {normalize_person_name(contact.name) for contact in profile_contacts}
    card_contacts, card_rejections = extract_card_level_contacts(roster_entries, institution, page_cache, covered_names)
    report.rejections.extend(card_rejections)

    update_activity(f"✨ Finishing {institution.name}...")
    personal_contacts = deduplicate_contacts(
        evidence_contacts + profile_contacts + card_contacts + pdf_contacts
    )
    if personal_contacts:
        report.contacts_found = len(personal_contacts)
        report.status = "Verified contacts found"
        return personal_contacts, report

    fallback_result = best_published_fallback(department_pages, page_cache)
    if fallback_result:
        return fallback_result

    report.status = "No public personal faculty email found"
    return [], report


def format_elapsed(seconds: float) -> str:
    total_seconds = max(0, int(round(seconds)))
    minutes, remaining_seconds = divmod(total_seconds, 60)
    if minutes:
        return f"{minutes}m {remaining_seconds:02d}s"
    return f"{remaining_seconds}s"


# ==================================================
# 15. Streamlit interface
# ==================================================

st.set_page_config(page_title=APP_NAME, page_icon="GM", layout="wide")

watermark_path = Path(__file__).parent / "assets" / "aventis-conference-watermark.png"
watermark_data = ""
if watermark_path.exists():
    watermark_data = base64.b64encode(watermark_path.read_bytes()).decode("ascii")

st.markdown(
    f"""
    <style>
    .stApp::before {{
        content: "";
        position: fixed;
        inset: 0;
        z-index: 0;
        pointer-events: none;
        background: url("data:image/png;base64,{watermark_data}") right center / cover no-repeat;
        opacity: 0.055;
        animation: aventis-watermark-drift 22s ease-in-out infinite alternate;
    }}
    .stApp > * {{ position: relative; z-index: 1; }}
    @keyframes aventis-watermark-drift {{
        from {{ transform: translate3d(0, 0, 0) scale(1); opacity: 0.045; }}
        to {{ transform: translate3d(0.8rem, -0.35rem, 0) scale(1.015); opacity: 0.075; }}
    }}
    @media (prefers-reduced-motion: reduce) {{
        .stApp::before {{ animation: none; }}
    }}
    .block-container {{ max-width: 1180px; padding-top: 1.5rem; }}
    .aventis-brand {{
        display: flex;
        align-items: center;
        gap: 0.7rem;
        margin-bottom: 1.1rem;
        color: #dbeafe;
        letter-spacing: 0;
    }}
    .aventis-monogram {{
        display: grid;
        place-items: center;
        width: 2.4rem;
        height: 2.4rem;
        color: #ffffff;
        background: #0877b9;
        border-left: 0.3rem solid #57c66c;
        border-radius: 6px;
        font-size: 1.45rem;
        font-weight: 800;
    }}
    .aventis-wordmark {{ font-size: 1rem; font-weight: 700; line-height: 1.05; }}
    .aventis-wordmark small {{
        display: block;
        color: #74c9ee;
        font-size: 0.66rem;
        margin-top: 0.22rem;
    }}
    button[data-testid="stBaseButton-primary"] {{
        background: #0877b9;
        border-color: #0877b9;
        color: #ffffff;
    }}
    button[data-testid="stBaseButton-primary"]:hover {{
        background: #005b91;
        border-color: #005b91;
    }}
    div[data-testid="stMetric"] {{
        border: 1px solid #e6e8ef;
        border-radius: 8px;
        padding: 0.65rem 0.8rem;
        background: #fbfcff;
    }}
    div[data-testid="stMetric"] [data-testid="stMetricLabel"],
    div[data-testid="stMetric"] [data-testid="stMetricValue"] {{
        color: #101828;
    }}
    .small-note {{ color: #9ba7ba; font-size: 0.92rem; line-height: 1.45; }}
    @media (max-width: 640px) {{
        .block-container {{ padding-top: 3.75rem; }}
        .aventis-brand {{ margin-bottom: 0.8rem; }}
        .stApp::before {{ background-position: 72% center; opacity: 0.04; }}
    }}
    </style>
    """,
    unsafe_allow_html=True,
)

st.markdown(
    '<div class="aventis-brand"><span class="aventis-monogram">A</span>'
    '<span class="aventis-wordmark">AVENTIS<small>CONFERENCES</small></span></div>',
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
    with st.spinner("Discovering relevant institutions from official sources..."):
        institutions, institution_log = discover_institutions(
            country,
            country_code,
            region,
            region_code,
            region_kind,
            specialty,
            custom_keywords,
        )
    if institutions:
        st.success(f"Found {len(institutions)} relevant institution(s) from official sources.")
    else:
        st.warning("No relevant institutions were verified from the available official sources.")
    st.session_state.institutions = institutions
    st.session_state.institution_log = institution_log
    st.session_state.selected_institution_names = [item.name for item in institutions]
    st.session_state.contacts = []
    st.session_state.reports = []
    st.session_state.discovery_scope = current_scope

institutions: list[Institution] = deduplicate_institutions(st.session_state.institutions)
if institutions != st.session_state.institutions:
    st.session_state.institutions = institutions
    available_names = {item.name for item in institutions}
    st.session_state.selected_institution_names = [
        name for name in st.session_state.selected_institution_names if name in available_names
    ]
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
        started_at = time.perf_counter()
        failure_statuses = {
            "Website blocked automated access",
            "JavaScript-only directory",
            "Manual review required",
        }

        with st.status("🔍 Searching university websites...", expanded=True) as search_status:
            completed_feed = st.container()
            current_panel = st.empty()
            next_panel = st.empty()
            count_panel = st.empty()
            progress = st.progress(0)

            for index, institution in enumerate(selected, start=1):
                with current_panel.container():
                    st.info(f"🔎 **{institution.name}**")
                    activity_panel = st.empty()

                if index < len(selected):
                    next_panel.caption(f"⏳ Up next: {selected[index].name}")
                else:
                    next_panel.empty()
                count_panel.caption(f"{index - 1} of {len(selected)} institutions completed")

                def show_activity(message: str, panel=activity_panel) -> None:
                    panel.caption(message)

                contacts, report = process_institution(
                    institution=institution,
                    country=country,
                    region=region,
                    specialty=specialty,
                    custom_keywords=custom_keywords,
                    delay_seconds=delay_seconds,
                    country_code=country_code,
                    region_code=region_code,
                    region_kind=region_kind,
                    progress_callback=show_activity,
                )
                all_contacts.extend(contacts)
                reports.append(report)
                current_panel.empty()

                page_word = "page" if report.department_pages == 1 else "pages"
                if report.status in failure_statuses:
                    completed_feed.warning(f"⚠️ {institution.name} — search failed: {report.status}")
                else:
                    completed_feed.success(
                        f"✅ {institution.name} — {report.department_pages} relevant {page_word} found"
                    )

                count_panel.caption(f"{index} of {len(selected)} institutions completed")
                progress.progress(index / len(selected))

            current_panel.empty()
            next_panel.empty()
            elapsed = time.perf_counter() - started_at
            total_pages = sum(report.department_pages for report in reports)
            search_status.update(label="🎉 Search complete!", state="complete", expanded=True)
            st.success(f"✅ {len(reports)} institutions searched")
            st.caption(f"📄 {total_pages} relevant pages found")
            st.caption(f"⏱️ Completed in {format_elapsed(elapsed)}")

        st.session_state.contacts = deduplicate_contacts(all_contacts)
        st.session_state.reports = reports

contacts = st.session_state.contacts
reports = st.session_state.reports

if reports:
    review_statuses = {
        "Website blocked automated access",
        "JavaScript-only directory",
        "Manual review required",
    }
    summary_values = {
        "Institutions Searched": len(reports),
        "With Contacts": sum(1 for report in reports if report.contacts_found > 0),
        "Contacts": len(contacts),
        "No Public Email": sum(
            1 for report in reports
            if report.contacts_found == 0 and report.status not in review_statuses
        ),
        "Needs Review": sum(1 for report in reports if report.status in review_statuses),
    }
    summary_cols = st.columns(len(summary_values))
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
