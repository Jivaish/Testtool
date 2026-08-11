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

try:
    from playwright.sync_api import sync_playwright
except Exception:  # pragma: no cover - browser rendering is an optional fallback
    sync_playwright = None


# ==================================================
# 1. Imports and constants
# ==================================================

APP_NAME = "Global Medical Faculty Contact Finder"
DEFAULT_REQUEST_DELAY = 0.45
USER_AGENT = (
    "Mozilla/5.0 (compatible; GlobalMedicalFacultyContactFinder/1.0; "
    "+https://streamlit.io)"
)
HEADERS = {
    "User-Agent": USER_AGENT,
    "Accept-Language": "en-US,en;q=0.9",
}

# Embedded from the supplied medical artwork so app-only deployments retain it.
EMBEDDED_BACKGROUND_WEBP = (
    "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"
)

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
    "edurank.", "residencyadvisor.", "residencyprograms.io",
    "residentswap.", "programdirectory.", "yellowpages.", "medifind.",
    "clinicslist.", "academia.edu", "journals.lww.", "tools.apgo.",
    "masters-in-health-administration.", "medschoolinsiders.",
    "universitysupplystore.", "twstalker.",
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

SPECIALTY_UNIT_TERMS: dict[str, list[str]] = {
    "Obstetrics and Gynecology": [
        "obstetrics and gynecology",
        "obstetrics & gynecology",
        "ob/gyn",
        "obgyn",
        "women's reproductive health",
        "maternal-fetal medicine",
        "reproductive endocrinology and infertility",
        "reproductive endocrinology",
        "reproductive medicine",
        "gynecologic oncology",
        "gyn oncology",
        "urogynecology",
        "female pelvic medicine",
        "pelvic medicine",
        "minimally invasive gynecologic surgery",
        "family planning",
        "complex family planning",
        "reproductive health",
        "maternal health",
        "fetal medicine",
        "prenatal diagnosis",
        "high-risk pregnancy",
        "general obstetrics",
        "general gynecology",
        "academic specialists in general obstetrics and gynecology",
        "center for women's health",
        "women's health research",
        "reproductive sciences",
    ],
}

SPECIALTY_UNIT_GROUPS: dict[str, list[tuple[str, list[str]]]] = {
    "Obstetrics and Gynecology": [
        ("obgyn", ["obstetrics and gynecology", "obstetrics & gynecology", "ob/gyn", "obgyn"]),
        ("womens_reproductive_health", ["women's reproductive health"]),
        ("maternal_fetal_medicine", ["maternal-fetal medicine", "maternal fetal medicine", "mfm"]),
        (
            "reproductive_endocrinology",
            ["reproductive endocrinology and infertility", "reproductive endocrinology", "rei", "ivf"],
        ),
        ("reproductive_medicine", ["reproductive medicine"]),
        ("gynecologic_oncology", ["gynecologic oncology", "gynaecologic oncology", "gyn oncology"]),
        (
            "urogynecology",
            ["urogynecology", "urogynaecology", "female pelvic medicine", "pelvic medicine"],
        ),
        ("minimally_invasive_surgery", ["minimally invasive gynecologic surgery"]),
        ("family_planning", ["family planning", "complex family planning"]),
        ("reproductive_health", ["reproductive health"]),
        ("maternal_fetal_health", ["maternal health", "fetal medicine", "maternal medicine"]),
        ("prenatal_high_risk", ["prenatal diagnosis", "high-risk pregnancy"]),
        (
            "general_obgyn",
            [
                "general obstetrics",
                "general gynecology",
                "academic specialists in general obstetrics and gynecology",
            ],
        ),
        ("womens_health_center", ["center for women's health", "women's health research"]),
        ("reproductive_sciences", ["reproductive sciences"]),
    ],
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


def specialty_unit_terms(specialty: str, terms: list[str]) -> list[str]:
    candidates = list(SPECIALTY_UNIT_TERMS.get(specialty, []))
    candidates.extend(terms)
    seen: set[str] = set()
    return [
        clean_term(term)
        for term in candidates
        if clean_term(term) and not (clean_term(term) in seen or seen.add(clean_term(term)))
    ]


def specialty_unit_groups(
    specialty: str,
    terms: list[str],
) -> list[tuple[str, list[str]]]:
    requested_terms = specialty_unit_terms(specialty, terms)
    configured = SPECIALTY_UNIT_GROUPS.get(specialty, [])
    groups: list[tuple[str, list[str]]] = []
    covered: set[str] = set()
    for intent, aliases in configured:
        cleaned_aliases = [clean_term(alias) for alias in aliases if clean_term(alias)]
        if cleaned_aliases:
            groups.append((intent, cleaned_aliases))
            covered.update(cleaned_aliases)
    groups.extend((term, [term]) for term in requested_terms if term not in covered)
    return groups


def search_alias_clause(aliases: list[str]) -> str:
    quoted = [f'"{alias}"' for alias in aliases]
    return quoted[0] if len(quoted) == 1 else f"({' OR '.join(quoted)})"


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
    additional_hosts: list[str] = field(default_factory=list)
    additional_evidence_urls: list[str] = field(default_factory=list)


@dataclass
class PageCandidate:
    url: str
    title: str
    matched_terms: list[str]
    source: str
    score: int
    classification: str = "UNCLASSIFIED"


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
    profile_url: str = ""
    email_source_url: str = ""
    relevance_evidence: str = ""
    confidence: str = ""

    def __post_init__(self) -> None:
        if not self.email_source_url:
            self.email_source_url = self.source_url
        if not self.profile_url and "profile" in self.method.casefold():
            self.profile_url = self.source_url
        if not self.relevance_evidence:
            self.relevance_evidence = self.method
        if not self.confidence:
            self.confidence = "HIGH" if self.strength == 0 else "MEDIUM"

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


@dataclass(frozen=True)
class SpecialtyEvidence:
    verified: bool
    regional_program: bool
    kind: str
    reason: str
    confidence: int


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
        "libguides", "medicine", "med", "news", "nursing", "online", "people",
        "portal", "research", "school", "som", "staff",
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


def institution_hosts(institution: Institution) -> list[str]:
    seen: set[str] = set()
    return [
        host
        for host in [institution.host, *institution.additional_hosts]
        if host and not (host in seen or seen.add(host))
    ]


def institution_related_domain(url_or_host: str, institution: Institution) -> bool:
    return any(
        related_official_domain(url_or_host, host)
        for host in institution_hosts(institution)
    )


def institution_search_hosts(institution: Institution) -> list[str]:
    """Return verified hosts plus their parent institutional domains for web search."""
    seen: set[str] = set()
    hosts: list[str] = []
    for host in institution_hosts(institution):
        parent = organization_root(host)
        for candidate in (host, parent):
            if candidate and not (candidate in seen or seen.add(candidate)):
                hosts.append(candidate)
    return hosts


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


def render_dynamic_html(url: str) -> tuple[str | None, str | None, str | None]:
    if sync_playwright is None:
        return None, url, "Playwright is not available"
    try:
        with sync_playwright() as playwright:
            browser_paths = (
                Path("/usr/bin/chromium"),
                Path("/usr/bin/chromium-browser"),
                Path("/usr/bin/google-chrome"),
                Path("C:/Program Files/Google/Chrome/Application/chrome.exe"),
                Path("C:/Program Files (x86)/Google/Chrome/Application/chrome.exe"),
                Path("C:/Program Files/Microsoft/Edge/Application/msedge.exe"),
            )
            executable = next((path for path in browser_paths if path.exists()), None)
            launch_options = {"headless": True}
            if executable:
                launch_options["executable_path"] = str(executable)
            browser = playwright.chromium.launch(**launch_options)
            page = browser.new_page(user_agent=USER_AGENT)
            page.goto(url, wait_until="domcontentloaded", timeout=DEFAULT_TIMEOUT * 1000)
            page.wait_for_timeout(1200)
            html = page.content()
            final_url = page.url
            browser.close()
            return html, final_url, None
    except Exception as exc:
        return None, url, f"Playwright {exc.__class__.__name__}"


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


@dataclass(frozen=True)
class PlannedSearch:
    query: str
    phase: str
    intent: str


class SearchProvider:
    name = "search-provider"

    def search(self, query: str, search_region: str = "wt-wt") -> list[dict[str, str]]:
        raise NotImplementedError


class DDGSSearchProvider(SearchProvider):
    name = "ddgs-auto"

    def search(self, query: str, search_region: str = "wt-wt") -> list[dict[str, str]]:
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
                            results.append(
                                {
                                    "url": href,
                                    "title": title,
                                    "body": body,
                                    "query": query,
                                    "provider": self.name,
                                }
                            )
            except Exception:
                results = []
            if results:
                return results
            if attempt == 0:
                time.sleep(0.4)
        return []


DEFAULT_SEARCH_PROVIDER = DDGSSearchProvider()


def search_web(
    query: str,
    search_region: str = "wt-wt",
    provider: SearchProvider | None = None,
) -> list[dict[str, str]]:
    return (provider or DEFAULT_SEARCH_PROVIDER).search(query, search_region)


def ddg_search(query: str, search_region: str = "wt-wt") -> list[dict[str, str]]:
    """Backward-compatible entry point used by existing integrations and tests."""
    return search_web(query, search_region, DEFAULT_SEARCH_PROVIDER)


def execute_search_round(
    searches: list[PlannedSearch],
    search_region: str,
    provider: SearchProvider | None = None,
) -> list[tuple[PlannedSearch, list[dict[str, str]]]]:
    if not searches:
        return []

    def run(search: PlannedSearch) -> tuple[PlannedSearch, list[dict[str, str]]]:
        results = search_web(search.query, search_region, provider)
        for result in results:
            result["search_phase"] = search.phase
            result["search_intent"] = search.intent
        return search, results

    with ThreadPoolExecutor(max_workers=min(8, len(searches))) as executor:
        return list(executor.map(run, searches))


def domain_hints_for_country(country: str, country_code: str = "") -> list[str]:
    key = clean_term(country)
    hints = list(COUNTRY_DOMAIN_HINTS.get(key, []))
    code = country_code.casefold()
    if code and code != "us":
        hints.extend([f".{code}", f".ac.{code}", f".edu.{code}"])
    seen: set[str] = set()
    return [hint for hint in hints if not (hint in seen or seen.add(hint))]


def build_institution_query_plan(
    country: str,
    country_code: str,
    region: str,
    specialty: str,
    terms: list[str],
) -> list[PlannedSearch]:
    location = region or country
    primary_term = terms[0] if terms else specialty
    core_terms = [primary_term]
    core_terms.extend(term for term in terms[1:] if len(term.split()) == 1)
    core_terms = list(dict.fromkeys(term for term in core_terms if term))
    term_query = " OR ".join(f'"{term}"' for term in core_terms)
    location_query = f'"{location}"'
    searches = [
        PlannedSearch(f'{location_query} university official website -jobs -news', "explore", "university_identity"),
        PlannedSearch(f'{location_query} medical school official website -jobs -news', "explore", "medical_school_identity"),
        PlannedSearch(f'{location_query} osteopathic medical college official', "explore", "osteopathic_identity"),
        PlannedSearch(f'{location_query} osteopathic medical campus official', "explore", "osteopathic_campus"),
        PlannedSearch(f'{location_query} health sciences university official website', "explore", "health_sciences_identity"),
        PlannedSearch(f'{location_query} academic teaching hospital official website', "explore", "teaching_institution_identity"),
        PlannedSearch(f'{location_query} ({term_query}) faculty university official', "specialty", "faculty"),
        PlannedSearch(f'{location_query} ({term_query}) medical school faculty', "specialty", "medical_faculty"),
        PlannedSearch(f'{location_query} ({term_query}) college faculty directory', "specialty", "faculty_directory"),
        PlannedSearch(f'{location_query} "{specialty}" academic department faculty', "specialty", "academic_department"),
        PlannedSearch(f'{location_query} ({term_query}) university program curriculum', "specialty", "curriculum"),
        PlannedSearch(f'{location_query} ({term_query}) medical education clinical training', "specialty", "clinical_training"),
        PlannedSearch(f'{location_query} ({term_query}) clerkship clinical rotation university', "coverage", "clerkship"),
        PlannedSearch(
            f'{location_query} "{specialty}" required clerkship medical school curriculum',
            "coverage",
            "required_clerkship",
        ),
        PlannedSearch(f'{location_query} "{specialty}" clinical curriculum faculty contact', "coverage", "faculty_contact"),
        PlannedSearch(f'{location_query} ({term_query}) medical students site information', "coverage", "medical_students"),
        PlannedSearch(f'{location_query} ({term_query}) medical school partnership pathway', "coverage", "partnership"),
        PlannedSearch(f'{location_query} ({term_query}) residency fellowship academic', "coverage", "academic_training"),
        PlannedSearch(f'{location_query} ({term_query}) regional campus teaching site', "coverage", "regional_teaching"),
    ]
    for hint in domain_hints_for_country(country, country_code):
        searches.extend([
            PlannedSearch(f'site:{hint} "{region or country}" ({term_query}) faculty', "coverage", "country_domain_faculty"),
            PlannedSearch(
                f'site:{hint} "{region or country}" "{specialty}" department',
                "coverage",
                "country_domain_department",
            ),
            PlannedSearch(
                f'site:{hint} "{region or country}" "{specialty}" curriculum clerkship',
                "coverage",
                "country_domain_curriculum",
            ),
        ])
    seen: set[str] = set()
    return [search for search in searches if not (search.query in seen or seen.add(search.query))]


def build_institution_queries(
    country: str,
    country_code: str,
    region: str,
    specialty: str,
    terms: list[str],
) -> list[str]:
    return [
        search.query
        for search in build_institution_query_plan(country, country_code, region, specialty, terms)
    ]


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
    location: str = "",
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
        score += 10
    if location and contains_location_term(combined, location):
        score += 12
    if any(word in combined for word in ("faculty", "curriculum", "clerkship", "clinical training")):
        score += 8
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


def institution_result_signals(
    url: str,
    title: str,
    body: str,
    location: str,
    terms: list[str],
) -> set[str]:
    combined = fold_text(f"{url} {title} {body}")
    signals: set[str] = set()
    if is_academic_domain(host_of(url)) or any(word in combined for word in STRONG_INSTITUTION_WORDS):
        signals.add("academic")
    if any(fold_text(term) in combined for term in terms):
        signals.add("specialty")
    if not location or contains_location_term(combined, location):
        signals.add("location")
    if any(word in combined for word in ("faculty", "people", "directory", "professor")):
        signals.add("faculty")
    if any(
        word in combined
        for word in (
            "curriculum", "clerkship", "clinical rotation", "clinical training",
            "medical education", "teaching", "residency", "fellowship",
        )
    ):
        signals.add("teaching")
    if "official" in combined or is_academic_domain(host_of(url)):
        signals.add("official")
    return signals


def promising_institution_root(root: str) -> bool:
    folded = fold_text(root)
    return is_academic_domain(root) or any(
        marker in folded
        for marker in (
            "university", "college", "school", "medical", "medicine",
            "health", "hospital", "institute", "academy",
        )
    )


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
    def merge_aliases(target: Institution, source: Institution) -> None:
        for host in [source.host, *source.additional_hosts]:
            if host and host != target.host and host not in target.additional_hosts:
                target.additional_hosts.append(host)
        for evidence_url in [source.evidence_url, *source.additional_evidence_urls]:
            if (
                evidence_url
                and evidence_url != target.evidence_url
                and evidence_url not in target.additional_evidence_urls
            ):
                target.additional_evidence_urls.append(evidence_url)

    by_name: dict[str, Institution] = {}
    for item in institutions:
        if not valid_institution_name(item.name, item.host):
            continue
        key = institution_name_key(item.name)
        if not key:
            continue
        existing = by_name.get(key)
        if not existing:
            by_name[key] = item
        elif (
            item.score,
            int(is_academic_domain(item.host)),
            -len(item.official_url),
        ) > (
            existing.score,
            int(is_academic_domain(existing.host)),
            -len(existing.official_url),
        ):
            merge_aliases(item, existing)
            by_name[key] = item
        else:
            merge_aliases(existing, item)
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
    primary_candidates = [
        item
        for item in merged
        if any(marker in fold_text(item.name) for marker in ("university", "college", "school"))
    ]
    affiliated_units: set[int] = set()
    unit_markers = (
        "center", "centre", "institute", "hospital", "health system",
        "medical center", "medical centre", "clinic", "libguides", "library",
        "portal",
    )
    for child in merged:
        if not any(marker in fold_text(child.name) for marker in unit_markers):
            continue
        child_blob = re.sub(
            r"[^a-z0-9]+",
            "",
            fold_text(f"{child.name} {organization_root(child.host).split('.', 1)[0]}"),
        )
        parents = [
            parent
            for parent in primary_candidates
            if parent is not child
            and len(institution_name_initialism(parent.name)) >= 3
            and institution_name_initialism(parent.name) in child_blob
        ]
        if not parents:
            continue
        parent = max(parents, key=lambda item: item.score)
        merge_aliases(parent, child)
        affiliated_units.add(id(child))

    return sorted(
        [item for item in merged if id(item) not in affiliated_units],
        key=lambda item: (-item.score, item.name.casefold()),
    )


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


def classify_specialty_program_evidence(
    text: str,
    region: str,
    terms: list[str],
) -> SpecialtyEvidence:
    folded = re.sub(r"[^a-z0-9]+", " ", fold_text(text))
    direct_terms = [
        re.sub(r"[^a-z0-9]+", " ", fold_text(term)).strip()
        for term in terms
        if fold_text(term)
    ]
    direct_terms = list(dict.fromkeys(term for term in direct_terms if term))
    if not folded or not direct_terms:
        return SpecialtyEvidence(False, False, "none", "No specialty terms supplied", 0)

    primary = direct_terms[0]
    primary_aliases = {
        primary,
        *(
            term
            for term in direct_terms
            if len(re.sub(r"[^a-z0-9]", "", term)) <= 8
        ),
    }
    unit_markers = (
        "department", "division", "section", "center", "centre",
        "institute", "faculty", "academic unit", "research group",
    )
    academic_markers = (
        "faculty", "professor", "academic", "teaching", "research",
        "chair", "division chief", "program director", "medical education",
        "school of medicine", "college of medicine", "medical school",
        "residency", "fellowship", "clerkship", "medical students",
    )
    medical_identity_markers = (
        "school of medicine", "college of medicine", "medical school",
        "osteopathic medicine", "medical students", "medical education",
        "clinical education", "doctor of medicine", "doctor of osteopathic medicine",
    )
    required_training_markers = (
        "required clerkship", "core clerkship", "clinical clerkship",
        "clerkship", "clinical rotation", "core rotation", "third year",
        "third-year", "fourth year", "fourth-year", "clinical curriculum",
    )
    exact_program_markers = (
        "residency program", "fellowship program", "academic program",
        "graduate medical education",
    )
    regional_markers = (
        "partnership", "pathway", "regional campus", "clinical site",
        "training site", "teaching site", "clerkship", "clinical rotation",
        "medical education", "students spend", "campus",
    )

    matched_kind = "none"
    matched_reason = "Specialty mentioned without direct academic-unit or medical-training evidence"
    confidence = 0
    for term in direct_terms:
        start = 0
        while (position := folded.find(term, start)) >= 0:
            context = folded[max(0, position - 900): position + len(term) + 900]
            local_context = folded[max(0, position - 360): position + len(term) + 360]
            has_unit = any(marker in local_context for marker in unit_markers)
            has_academic_role = any(marker in local_context for marker in academic_markers)
            has_medical_identity = any(marker in context for marker in medical_identity_markers)
            has_required_training = any(marker in context for marker in required_training_markers)
            has_exact_program = any(marker in context for marker in exact_program_markers)

            if has_unit and has_academic_role:
                matched_kind = "academic_unit"
                matched_reason = f"Direct academic specialty unit or faculty evidence for {term}"
                confidence = 100
                break
            if term in primary_aliases and has_medical_identity and has_required_training:
                matched_kind = "medical_training"
                matched_reason = f"Required medical-school specialty training evidence for {term}"
                confidence = 90
                break
            if term in primary_aliases and has_medical_identity and has_exact_program:
                matched_kind = "academic_program"
                matched_reason = f"Direct academic specialty program evidence for {term}"
                confidence = 90
                break
            start = position + len(term)
        if matched_kind != "none":
            break

    regional_program = False
    region_term = re.sub(r"[^a-z0-9]+", " ", fold_text(region)).strip()
    if matched_kind != "none" and region_term:
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
    return SpecialtyEvidence(
        matched_kind != "none",
        regional_program,
        matched_kind,
        matched_reason,
        confidence,
    )


def specialty_program_evidence(
    text: str,
    region: str,
    terms: list[str],
) -> tuple[bool, bool]:
    evidence = classify_specialty_program_evidence(text, region, terms)
    return evidence.verified, evidence.regional_program


def official_source_specialty_evidence_details(
    source_url: str,
    official_host: str,
    region: str,
    terms: list[str],
) -> SpecialtyEvidence:
    normalized = normalize_url(source_url)
    if not normalized or not related_official_domain(normalized, official_host):
        return SpecialtyEvidence(False, False, "none", "Not an official institutional URL", 0)
    source_session = make_session()
    if is_pdf_url(normalized):
        text, error = fetch_pdf_text(source_session, normalized)
        if error or not text:
            return SpecialtyEvidence(False, False, "none", error or "Unreadable official PDF", 0)
        return classify_specialty_program_evidence(text, region, terms)
    html, final_url, _ = fetch_html(source_session, normalized)
    if not html or not final_url or not related_official_domain(final_url, official_host):
        return SpecialtyEvidence(False, False, "none", "Official evidence page unavailable", 0)
    soup = BeautifulSoup(html, "html.parser")
    return classify_specialty_program_evidence(soup.get_text(" ", strip=True), region, terms)


def official_source_specialty_evidence(
    source_url: str,
    official_host: str,
    region: str,
    terms: list[str],
) -> tuple[bool, bool]:
    evidence = official_source_specialty_evidence_details(
        source_url,
        official_host,
        region,
        terms,
    )
    return evidence.verified, evidence.regional_program


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
    query_plan = build_institution_query_plan(
        country,
        country_code,
        region,
        specialty,
        discovery_terms,
    )
    institutions_by_root: dict[str, Institution] = {}
    candidates_by_root: dict[str, dict[str, tuple[int, str, dict[str, str]]]] = {}
    log: list[str] = []
    search_region = search_region_for_country(country_code)
    executed_queries: set[str] = set()
    refined_roots: dict[str, set[str]] = {
        "faculty": set(),
        "curriculum": set(),
        "training": set(),
    }

    def add_search_result(
        search: PlannedSearch,
        result: dict[str, str],
        target_root: str = "",
    ) -> bool:
        normalized_result_url = normalize_url(result["url"])
        if not normalized_result_url:
            return False
        if target_root and not related_official_domain(normalized_result_url, target_root):
            return False

        candidate_url = canonical_institution_url(result["url"])
        if target_root:
            existing_payloads = candidates_by_root.get(target_root, {})
            if not existing_payloads:
                return False
            candidate_url = max(
                existing_payloads.values(),
                key=lambda payload: payload[0],
            )[2]["candidate_url"]
        if not candidate_url:
            return False
        root = target_root or institution_candidate_host(host_of(candidate_url))
        signals = institution_result_signals(
            result["url"],
            result["title"],
            result["body"],
            region or country,
            discovery_terms,
        )
        score = score_institution_result(
            result["url"],
            result["title"],
            result["body"],
            country,
            country_code,
            discovery_terms,
            region or country,
        )
        if score < 35:
            return False
        has_specialty_evidence = "specialty" in signals
        has_region_evidence = "location" in signals
        if target_root and any(
            payload[2].get("region_evidence") == "1"
            for payload in candidates_by_root[target_root].values()
        ):
            has_region_evidence = True
        enriched_result = {
            **result,
            "candidate_url": candidate_url,
            "specialty_evidence": "1" if has_specialty_evidence else "0",
            "region_evidence": "1" if has_region_evidence else "0",
            "evidence_signals": ",".join(sorted(signals)),
            "search_phase": search.phase,
            "search_intent": search.intent,
        }
        was_new_root = root not in candidates_by_root
        root_candidates = candidates_by_root.setdefault(root, {})
        evidence_key = normalized_result_url
        existing_candidate = root_candidates.get(evidence_key)
        new_rank = (
            int(has_specialty_evidence),
            int(has_specialty_evidence and has_region_evidence),
            len(signals),
            score,
        )
        existing_rank = (
            int(bool(existing_candidate and existing_candidate[2]["specialty_evidence"] == "1")),
            int(bool(
                existing_candidate
                and existing_candidate[2]["specialty_evidence"] == "1"
                and existing_candidate[2].get("region_evidence") == "1"
            )),
            len(existing_candidate[2].get("evidence_signals", "").split(",")) if existing_candidate else 0,
            existing_candidate[0] if existing_candidate else -1000,
        )
        if not existing_candidate or new_rank > existing_rank:
            root_candidates[evidence_key] = (score, search.query, enriched_result)
        return was_new_root

    term_query = " OR ".join(f'"{term}"' for term in discovery_terms)

    def collect_round(
        searches: list[PlannedSearch],
        targets_by_query: dict[str, str] | None = None,
    ) -> set[str]:
        pending = [search for search in searches if search.query not in executed_queries]
        for search in pending:
            executed_queries.add(search.query)
        new_roots: set[str] = set()
        for search, results in execute_search_round(pending, search_region):
            accepted = 0
            target_root = (targets_by_query or {}).get(search.query, "")
            for result in results:
                if add_search_result(search, result, target_root):
                    new_roots.add(target_root or institution_candidate_host(host_of(result["url"])))
                normalized = normalize_url(result["url"])
                if normalized:
                    if target_root:
                        stored = normalized in candidates_by_root.get(target_root, {})
                    else:
                        stored = any(
                            normalized in payloads
                            for payloads in candidates_by_root.values()
                        )
                    accepted += int(stored)
            log.append(
                f"[{search.phase}/{search.intent}] {search.query}: "
                f"{len(results)} result(s), {accepted} candidate evidence item(s)"
            )
        return new_roots

    def evidence_gap_roots() -> list[str]:
        return [
            root
            for root, payloads in candidates_by_root.items()
            if payloads
            and not any(payload[2]["specialty_evidence"] == "1" for payload in payloads.values())
            and max(payload[0] for payload in payloads.values()) >= 45
            and any(payload[2].get("region_evidence") == "1" for payload in payloads.values())
            and promising_institution_root(root)
        ]

    def unresolved_roots(intent: str) -> list[str]:
        return [
            root
            for root in evidence_gap_roots()
            if root not in refined_roots[intent]
        ]

    def refine_missing_specialty(intent: str) -> None:
        roots = unresolved_roots(intent)
        searches: list[PlannedSearch] = []
        targets_by_query: dict[str, str] = {}
        for root in roots:
            if intent == "faculty":
                query = f'site:{root} ({term_query}) (department OR faculty OR "faculty directory")'
            elif intent == "curriculum":
                query = (
                    f'site:{root} ({term_query}) '
                    '(curriculum OR clerkship OR "clinical rotation" OR teaching)'
                )
            else:
                primary = discovery_terms[0] if discovery_terms else specialty
                short_aliases = [
                    term
                    for term in discovery_terms
                    if len(re.sub(r"[^a-z0-9]", "", term.casefold())) <= 8
                ]
                focused_terms = [primary, *short_aliases]
                focused_query = " OR ".join(
                    f'"{term}"' for term in dict.fromkeys(focused_terms)
                )
                query = (
                    f'site:{root} ({focused_query}) '
                    '("required clerkship" OR "clinical rotation" OR curriculum '
                    'OR "clinical education" OR "third year")'
                )
            searches.append(PlannedSearch(query, "refine", intent))
            targets_by_query[query] = root
            refined_roots[intent].add(root)
        if searches:
            collect_round(searches, targets_by_query)

    initial_searches = [search for search in query_plan if search.phase in {"explore", "specialty"}]
    collect_round(initial_searches)
    refine_missing_specialty("faculty")
    refine_missing_specialty("curriculum")
    refine_missing_specialty("training")

    core_coverage_intents = {
        "clerkship", "required_clerkship", "partnership", "regional_teaching",
        "country_domain_faculty", "country_domain_department", "country_domain_curriculum",
    }
    core_coverage = [
        search
        for search in query_plan
        if search.phase == "coverage" and search.intent in core_coverage_intents
    ]
    collect_round(core_coverage)
    refine_missing_specialty("faculty")
    refine_missing_specialty("curriculum")
    refine_missing_specialty("training")

    has_specialty_roots = any(
        any(payload[2]["specialty_evidence"] == "1" for payload in payloads.values())
        for payloads in candidates_by_root.values()
    )
    remaining_coverage = [
        search
        for search in query_plan
        if search.phase == "coverage" and search.intent not in core_coverage_intents
    ]
    remaining_gaps = evidence_gap_roots()
    if not has_specialty_roots or remaining_gaps:
        collect_round(remaining_coverage)
        refine_missing_specialty("faculty")
        refine_missing_specialty("curriculum")
        refine_missing_specialty("training")
    else:
        log.append("[coverage] Extended searches skipped because evidence gaps converged.")

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
        ) -> tuple[tuple[int, str, dict[str, str]], SpecialtyEvidence]:
            payload_result = payload[2]
            evidence = official_source_specialty_evidence_details(
                payload_result["url"],
                host_of(payload_result["url"]),
                region,
                discovery_terms,
            )
            return payload, evidence

        with ThreadPoolExecutor(max_workers=min(6, len(eligible_payloads) or 1)) as executor:
            evidence_checks = list(executor.map(check_evidence, eligible_payloads))
        verified_evidence = [item for item in evidence_checks if item[1].verified]
        if not verified_evidence:
            message = f"Rejected {candidate_url}: official source did not verify {specialty} teaching or training"
            return root, None, message
        evidence_payload, evidence_details = max(
            verified_evidence,
            key=lambda item: (
                item[1].confidence,
                int(item[1].regional_program),
                int(item[0][2].get("region_evidence") == "1"),
                item[0][0],
            ),
        )
        regional_program_verified = evidence_details.regional_program
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
        return root, item, (
            f"Accepted {name}: {candidate_url} "
            f"({evidence_details.kind}: {evidence_result['url']})"
        )

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


PAGE_CLASSIFICATIONS = {
    "DEPARTMENT",
    "DIVISION",
    "FACULTY_DIRECTORY",
    "PERSON_PROFILE",
    "CENTER",
    "HOSPITAL_PROVIDER",
    "SEARCH_RESULT",
    "IRRELEVANT",
}


def classify_official_page(
    url: str,
    title: str,
    page_text: str,
    html: str = "",
) -> str:
    path = urlparse(url).path.casefold()
    header = fold_text(f"{title} {page_text[:1800]}")
    structured = fold_text(html[:12000])
    if (
        '"@type":"person"' in structured.replace(" ", "")
        or any(marker in path for marker in ("/profile/", "/profiles/", "/person/", "/provider/"))
    ):
        return "PERSON_PROFILE"
    if any(marker in header for marker in ("faculty directory", "our faculty", "faculty staff", "our team")):
        return "FACULTY_DIRECTORY"
    if "division" in header or "/division" in path:
        return "DIVISION"
    if any(marker in header for marker in ("center for", "centre for", "research center", "research centre")):
        return "CENTER"
    if "department" in header or "/department" in path:
        return "DEPARTMENT"
    if any(marker in header for marker in ("find a provider", "find a doctor", "physician profile")):
        return "HOSPITAL_PROVIDER"
    if any(marker in header for marker in ("faculty", "professor", "researcher", "physician")):
        return "FACULTY_DIRECTORY"
    return "IRRELEVANT"


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


def build_department_query_plan(
    host: str,
    region: str,
    specialty: str,
    terms: list[str],
) -> list[PlannedSearch]:
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
    searches = [
        PlannedSearch(f"site:{host} {primary} faculty", "department", "faculty"),
        PlannedSearch(
            f"site:{host} {specialty} department faculty",
            "department",
            "academic_department",
        ),
        PlannedSearch(f"site:{host} {primary} people directory", "department", "directory"),
        PlannedSearch(f"site:{host} {primary} academic staff", "department", "academic_staff"),
        PlannedSearch(f"site:{host} {region} {primary} faculty", "department", "regional_faculty"),
        PlannedSearch(f'site:{host} "{short_alias}" faculty email', "contact", "faculty_email"),
        PlannedSearch(
            f'site:{host} "{specialty}" department contact',
            "contact",
            "department_contact",
        ),
        PlannedSearch(
            f'site:{host} "{primary}" program coordinator',
            "contact",
            "program_contact",
        ),
        PlannedSearch(
            f'site:{host} "@{email_domain}" "{short_alias}"',
            "contact",
            "published_email",
        ),
        PlannedSearch(
            f'site:{host} orientation "{short_alias}" faculty',
            "documents",
            "orientation_document",
        ),
        PlannedSearch(
            f'site:{host} onboarding "{short_alias}" faculty',
            "documents",
            "onboarding_document",
        ),
    ]
    document_aliases = [alias for alias in ("ob/gyn", "ob-gyn") if alias in terms and alias != short_alias]
    for alias in document_aliases:
        searches.extend(
            [
                PlannedSearch(
                    f'site:{host} orientation "{alias}" faculty',
                    "documents",
                    "orientation_document",
                ),
                PlannedSearch(
                    f'site:{host} "@{email_domain}" "{alias}"',
                    "contact",
                    "published_email",
                ),
            ]
        )
    for unit_intent, unit_aliases in specialty_unit_groups(specialty, terms):
        searches.append(
            PlannedSearch(
                f"site:{host} {search_alias_clause(unit_aliases)} "
                '(faculty OR people OR physicians OR researchers OR directory)',
                "units",
                unit_intent,
            )
        )
    seen: set[str] = set()
    return [search for search in searches if not (search.query in seen or seen.add(search.query))]


def department_search_result_signals(
    item: dict[str, str],
    email_domain: str,
) -> set[str]:
    source_text = f'{item.get("url", "")} {item.get("title", "")} {item.get("body", "")}'
    text = fold_text(source_text)
    signals: set[str] = set()
    if any(word in text for word in ("faculty", "professor", "directory", "academic staff", "people")):
        signals.add("faculty")
    if (
        f"@{email_domain}" in source_text.casefold()
        or re.search(r"\b(?:email|contact|coordinator|program office)\b", text)
    ):
        signals.add("email")
    if any(word in text for word in ("orientation", "onboarding", "handbook", "directory pdf")):
        signals.add("document")
    if urlparse(item.get("url", "")).path.casefold().endswith((".pdf", ".doc", ".docx")):
        signals.add("document")
    return signals


def site_search_department_urls(
    host: str,
    region: str,
    specialty: str,
    terms: list[str],
    search_region: str = "wt-wt",
    provider: SearchProvider | None = None,
) -> list[dict[str, str]]:
    query_plan = build_department_query_plan(host, region, specialty, terms)
    email_domain = organization_root(host)
    results: list[dict[str, str]] = []
    seen: set[str] = set()

    def collect(searches: list[PlannedSearch]) -> set[str]:
        round_signals: set[str] = set()
        for search, search_results in execute_search_round(searches, search_region, provider):
            for item in search_results:
                round_signals.update(department_search_result_signals(item, email_domain))
                url = normalize_url(item.get("url", ""))
                if not url or url in seen or not related_official_domain(url, host):
                    continue
                record = dict(item)
                record["url"] = url
                record["query"] = search.query
                record["search_phase"] = search.phase
                record["search_intent"] = search.intent
                seen.add(url)
                results.append(record)
        return round_signals

    observed_signals = collect(
        [search for search in query_plan if search.phase == "department"]
    )
    observed_signals.update(
        collect([search for search in query_plan if search.phase == "units"])
    )
    if "email" not in observed_signals:
        observed_signals.update(
            collect([search for search in query_plan if search.phase == "contact"])
        )
    if "document" not in observed_signals and not {"faculty", "email"}.issubset(observed_signals):
        collect([search for search in query_plan if search.phase == "documents"])
    return results


def build_faculty_audit_query_plan(
    host: str,
    specialty: str,
    terms: list[str],
    compact: bool = False,
) -> list[PlannedSearch]:
    unit_groups = specialty_unit_groups(specialty, terms)
    if compact:
        clauses = [search_alias_clause(aliases) for _, aliases in unit_groups]
        searches = [
            PlannedSearch(
                f"site:{host} ({' OR '.join(chunk)}) "
                '(professor OR faculty OR physician OR researcher OR "program director") -jobs',
                "audit",
                f"affiliate_units_{index // 4 + 1}",
            )
            for index in range(0, len(clauses), 4)
            for chunk in [clauses[index:index + 4]]
        ]
    else:
        searches = [
            PlannedSearch(
                f"site:{host} {search_alias_clause(unit_aliases)} "
                '(professor OR faculty OR physician OR researcher OR "program director") -jobs',
                "audit",
                unit_intent,
            )
            for unit_intent, unit_aliases in unit_groups
        ]
    searches.extend(
        [
            PlannedSearch(
                f'site:{host} "{specialty}" residency faculty',
                "audit",
                "residency_faculty",
            ),
            PlannedSearch(
                f'site:{host} "{specialty}" fellowship faculty',
                "audit",
                "fellowship_faculty",
            ),
            PlannedSearch(
                f'site:{host} "{specialty}" research faculty',
                "audit",
                "research_faculty",
            ),
        ]
    )
    seen: set[str] = set()
    return [search for search in searches if not (search.query in seen or seen.add(search.query))]


def discover_second_pass_pages(
    institution: Institution,
    specialty: str,
    terms: list[str],
    existing_urls: Iterable[str],
    disallowed_paths: list[str],
    country_code: str = "",
    compact: bool = False,
) -> tuple[list[PageCandidate], dict[str, str], list[str]]:
    searches = [
        search
        for host_index, host in enumerate(institution_search_hosts(institution))
        for search in build_faculty_audit_query_plan(
            host,
            specialty,
            terms,
            compact=compact or host_index > 0,
        )
    ]
    existing = {normalize_url(url) for url in existing_urls}
    discovered: dict[str, tuple[PlannedSearch, dict[str, str]]] = {}
    log: list[str] = []
    for search, results in execute_search_round(
        searches,
        search_region_for_country(country_code),
    ):
        accepted = 0
        for item in results:
            normalized = normalize_url(item.get("url", ""))
            if (
                not normalized
                or normalized in existing
                or not institution_related_domain(normalized, institution)
                or not path_allowed(normalized, disallowed_paths)
            ):
                continue
            discovered.setdefault(normalized, (search, item))
            accepted += 1
        log.append(
            f"[audit/{search.intent}] {search.query}: "
            f"{len(results)} result(s), {accepted} new official URL(s)"
        )

    def verify_page(
        payload: tuple[str, tuple[PlannedSearch, dict[str, str]]],
    ) -> tuple[PageCandidate | None, str, str]:
        url, (search, item) = payload
        session = make_session()
        if is_pdf_url(url):
            text, error = fetch_pdf_text(session, url)
            if not text:
                return None, "", f"Rejected {url}: {error or 'unreadable PDF'}"
            evidence = classify_specialty_program_evidence(text, "", terms)
            classification = "FACULTY_DIRECTORY" if "faculty" in fold_text(text[:2500]) else "SEARCH_RESULT"
            html = ""
            title = clean_text(item.get("title", ""))
        else:
            html, final_url, error = fetch_html(session, url)
            if not html or not final_url:
                return None, "", f"Rejected {url}: {error or 'unavailable'}"
            if not institution_related_domain(final_url, institution):
                return None, "", f"Rejected {url}: left the official domain"
            url = final_url
            soup = BeautifulSoup(html, "html.parser")
            title = clean_text(soup.title.get_text(" ", strip=True) if soup.title else item.get("title", ""))
            text = clean_text(soup.get_text(" ", strip=True))
            evidence = classify_specialty_program_evidence(text, "", terms)
            classification = classify_official_page(url, title, text, html)

        matched = text_matches_terms(f"{url} {title} {text[:4000]}", terms)
        if not matched:
            return None, "", f"Rejected {url}: no specialty evidence in official content"
        if not evidence.verified and classification not in {"FACULTY_DIRECTORY", "PERSON_PROFILE"}:
            return None, "", f"Rejected {url}: {evidence.reason}"

        path = urlparse(url).path.casefold()
        last_path_part = path.rstrip("/").rsplit("/", 1)[-1]
        identity_text = f"{url} {title}"
        identity_matches_specialty = text_matches_terms(identity_text, terms)
        explicit_person_path = any(
            marker in path
            for marker in (
                "/profile/", "/profiles/", "/person/", "/provider/",
                "/faculty-and-staff/bio/", "/faculty/bio/", "/bio/", "/bios/",
            )
        )
        directory_path = any(
            marker in path
            for marker in (
                "/faculty", "/people", "/our-team", "/team", "/providers",
                "/physicians", "/directory",
            )
        )
        directory_title = any(
            marker in fold_text(title)
            for marker in ("faculty directory", "our faculty", "faculty and staff", "our team")
        )
        person_path = explicit_person_path or (
            looks_like_profile_url(url, title)
            and last_path_part not in {
                "index", "index.html", "index.php", "default", "default.html",
                "faculty", "staff", "people", "directory",
            }
            and not directory_title
        )
        unit_identity = identity_matches_specialty and evidence.verified and any(
            marker in fold_text(identity_text)
            for marker in (
                "department", "division", "center", "centre", "institute",
                "program", "residency", "fellowship", "research",
            )
        )
        faculty_capable = (
            person_path
            or ((directory_path or directory_title) and identity_matches_specialty)
            or unit_identity
            or (is_pdf_url(url) and evidence.verified and "faculty" in fold_text(text[:5000]))
        )
        if not faculty_capable:
            return None, "", f"Rejected {url}: not a specialty-focused faculty source"
        if person_path:
            classification = "PERSON_PROFILE"
        score = relevance_score(url, title, text, terms) + evidence.confidence
        page = PageCandidate(url, title, matched, "second_pass_audit", score, classification)
        return page, html, f"Accepted {url}: {classification} ({search.intent})"

    pages: dict[str, PageCandidate] = {}
    page_cache: dict[str, str] = {}
    with ThreadPoolExecutor(max_workers=min(8, len(discovered) or 1)) as executor:
        for page, html, message in executor.map(verify_page, discovered.items()):
            log.append(message)
            if page:
                pages[page.url] = page
                if html:
                    page_cache[page.url] = html
    return sorted(pages.values(), key=lambda page: (-page.score, page.url)), page_cache, log


def discover_verified_specialty_affiliates(
    evidence_soup: BeautifulSoup,
    evidence_url: str,
    institution: Institution,
    region: str,
    terms: list[str],
) -> list[tuple[str, str, str, str, str]]:
    """Verify external specialty sites linked by an official academic evidence page."""
    candidates: dict[str, str] = {}
    link_markers = (
        "department", "division", "faculty", "academic", "program", "centre",
        "center", "institute", "research", "residency", "fellowship", "website",
    )
    for anchor in evidence_soup.find_all("a", href=True):
        link = normalize_url(urljoin(evidence_url, anchor.get("href", "")))
        if not link or institution_related_domain(link, institution) or is_bad_external_source(link):
            continue
        label = clean_text(anchor.get_text(" ", strip=True))
        parent_text = ""
        if isinstance(anchor.parent, Tag):
            parent_text = clean_text(anchor.parent.get_text(" ", strip=True))[:500]
        link_evidence = f"{link} {label} {parent_text}"
        if not text_matches_terms(link_evidence, terms):
            continue
        if not any(marker in fold_text(link_evidence) for marker in link_markers):
            continue
        candidates.setdefault(link, label)

    def verify(candidate: tuple[str, str]) -> tuple[str, str, str, str, str] | None:
        candidate_url, _ = candidate
        html, final_url, _ = fetch_html(make_session(), candidate_url)
        if not html or not final_url or is_bad_external_source(final_url):
            return None
        final_host = host_of(final_url)
        if not final_host:
            return None
        soup = BeautifulSoup(html, "html.parser")
        title = clean_text(soup.title.get_text(" ", strip=True) if soup.title else "")
        page_text = clean_text(soup.get_text(" ", strip=True))
        specialty_evidence = classify_specialty_program_evidence(page_text, region, terms)
        classification = classify_official_page(final_url, title, page_text, html)
        backlink = any(
            institution_related_domain(
                normalize_url(urljoin(final_url, linked.get("href", ""))) or "",
                institution,
            )
            for linked in soup.find_all("a", href=True)
        )
        named_parent = fold_text(institution.name) in fold_text(page_text)
        if (
            not specialty_evidence.verified
            or classification == "IRRELEVANT"
            or not (backlink or named_parent)
        ):
            return None
        return final_url, final_host, html, title, page_text

    if not candidates:
        return []
    with ThreadPoolExecutor(max_workers=min(6, len(candidates))) as executor:
        return [item for item in executor.map(verify, candidates.items()) if item]


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
        if not normalized or not institution_related_domain(normalized, institution):
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
            or (source in {"discovery_evidence", "verified_affiliate"} and bool(matched))
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
        if source not in {"homepage", "discovery_evidence", "verified_affiliate"} and not is_pdf and not (
            strong_directory_seed or exact_specialty_title or short_path_match
        ):
            return
        score = relevance_score(normalized, title, page_text, terms)
        if strong_directory_seed:
            score = max(score, 25)
        if score <= 0:
            return
        classification = classify_official_page(normalized, title, page_text)
        item = PageCandidate(
            normalized,
            clean_text(title),
            matched,
            source,
            score,
            classification,
        )
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
            and institution_related_domain(evidence_final_url, institution)
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

            verified_affiliates = discover_verified_specialty_affiliates(
                evidence_soup,
                evidence_final_url,
                institution,
                region,
                terms,
            )
            for affiliate_url, affiliate_host, affiliate_html, affiliate_title, affiliate_text in verified_affiliates:
                if affiliate_host not in institution.additional_hosts:
                    institution.additional_hosts.append(affiliate_host)
                page_cache[affiliate_url] = affiliate_html
                add_candidate(
                    affiliate_url,
                    affiliate_title,
                    "verified_affiliate",
                    affiliate_text,
                )
                log.append(f"Verified specialty affiliate: {affiliate_host}")

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

    for search_host in institution_search_hosts(institution):
        for item in site_search_department_urls(
            search_host,
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
        if not institution_related_domain(final_candidate, institution):
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
        target = normalize_url(urljoin(base_url, anchor.get("href", "")))
        if not target or target == normalize_url(base_url):
            continue
        pagination_parent = anchor.find_parent(
            attrs={
                "class": re.compile(r"pag(?:e|ination)|pager", re.I),
            }
        )
        numeric_page_url = bool(
            re.search(r"(?:[?&](?:page|start|offset)=\d+|/page/\d+(?:/|$))", target, flags=re.I)
        )
        if (
            text in NEXT_LINK_WORDS
            or aria in NEXT_LINK_WORDS
            or "next" in aria
            or (text.isdigit() and (pagination_parent or numeric_page_url))
        ):
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
    if looks_like_profile_url(target_url, link_text):
        return False
    academic_link_markers = (
        "department", "division", "faculty", "people", "directory", "team",
        "leadership", "center", "centre", "institute", "research", "residency",
        "fellowship", "provider", "physician",
    )
    if text_matches_terms(combined, terms):
        return any(marker in combined for marker in academic_link_markers)
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
    path_parts = [part for part in urlparse(lowered_url).path.split("/") if part]
    if path_parts and path_parts[-1] in {
        "faculty", "people", "person", "profiles", "providers", "staff", "directory",
    }:
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
    "MLIS", "FACOI", "FACOFP", "FACEP", "FAAEM", "FACOOG", "MSCP", "FNPC", "MCR",
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
    "complex", "family", "planning", "oncology", "gynecology", "gynaecology",
    "obstetrics", "urogynecology", "urogynaecology", "endocrinology", "infertility",
    "pelvic", "maternal", "fetal", "reproductive",
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
    queue: deque[str] = deque()
    scheduled: set[str] = set()
    visited: set[str] = set()
    seen_content: set[tuple[int, str, str]] = set()
    roster: dict[str, FacultyEntry] = {}
    faculty_pages: list[str] = []
    rejections: list[Rejection] = []
    page_cache: dict[str, str] = dict(seed_cache or {})
    log: list[str] = []
    blocked: list[str] = []

    def enqueue(raw_url: str) -> None:
        normalized = normalize_url(raw_url)
        if not normalized or normalized in scheduled:
            return
        if not institution_related_domain(normalized, institution):
            return
        if not path_allowed(normalized, disallowed_paths):
            log.append(f"Skipped by robots.txt: {normalized}")
            return
        scheduled.add(normalized)
        queue.append(normalized)

    for page in department_pages:
        enqueue(page.url)

    def fetch_page(normalized: str) -> tuple[str, str | None, str | None, str | None]:
        cached = page_cache.get(normalized)
        if cached is not None:
            return normalized, cached, normalized, None
        page_session = make_session()
        html, final_url, error = fetch_html(page_session, normalized)
        if delay_seconds > 0:
            time.sleep(delay_seconds)
        return normalized, html, final_url, error

    with ThreadPoolExecutor(max_workers=6) as executor:
        while queue:
            batch: list[str] = []
            while queue and len(batch) < 18:
                normalized = queue.popleft()
                if normalized in visited:
                    continue
                visited.add(normalized)
                if is_pdf_url(normalized):
                    faculty_pages.append(normalized)
                    continue
                batch.append(normalized)

            if not batch:
                continue

            for normalized, html, final_url, error in executor.map(fetch_page, batch):
                if not html or not final_url:
                    blocked.append(f"{normalized}: {error or 'unavailable'}")
                    continue
                if not institution_related_domain(final_url, institution):
                    continue
                final_normalized = normalize_url(final_url)
                if final_normalized:
                    visited.add(final_normalized)
                    scheduled.add(final_normalized)
                page_cache[final_url] = html

                raw_soup = BeautifulSoup(html, "html.parser")
                raw_text = clean_text(raw_soup.get_text(" ", strip=True))
                raw_title = clean_text(
                    raw_soup.title.get_text(" ", strip=True) if raw_soup.title else ""
                )
                dynamic_identity = fold_text(f"{final_url} {raw_title}")
                dynamic_directory = any(
                    marker in dynamic_identity
                    for marker in (
                        "faculty", "people", "directory", "provider", "physician", "our team",
                    )
                )
                if dynamic_directory and page_has_js_only_signals(raw_soup, raw_text):
                    rendered_html, rendered_url, render_error = render_dynamic_html(final_url)
                    if (
                        rendered_html
                        and rendered_url
                        and institution_related_domain(rendered_url, institution)
                    ):
                        html = rendered_html
                        final_url = rendered_url
                        page_cache[final_url] = html
                        log.append(f"Rendered JavaScript directory: {final_url}")
                    else:
                        log.append(
                            f"Possible JavaScript-only directory: {final_url} "
                            f"({render_error or 'rendering unavailable'})"
                        )

                content_key = (len(html), html[:800], html[-800:])
                if content_key in seen_content:
                    log.append(f"Duplicate official mirror skipped: {final_url}")
                    continue
                seen_content.add(content_key)

                soup = BeautifulSoup(html, "html.parser")
                for tag in soup(["script", "style", "noscript", "nav", "footer", "form"]):
                    tag.decompose()
                title = clean_text(soup.title.get_text(" ", strip=True) if soup.title else "")
                page_text = clean_text(soup.get_text(" ", strip=True))
                combined_header = f"{final_url} {title}".lower()
                if any(word in combined_header for word in FACULTY_PAGE_WORDS):
                    faculty_pages.append(final_url)

                page_has_terms = bool(text_matches_terms(f"{final_url} {title} {page_text}", terms))
                if page_has_terms:
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
                        enqueue(page_link)

                for anchor in soup.find_all("a", href=True):
                    link = normalize_url(urljoin(final_url, anchor.get("href", "")))
                    if not link:
                        continue
                    link_text = clean_text(anchor.get_text(" ", strip=True))
                    if should_follow_faculty_link(
                        final_url,
                        link,
                        link_text,
                        page_has_terms,
                        terms,
                    ):
                        enqueue(link)

                log.append(f"[{len(visited)} checked] {final_url}")

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
    institution: Institution,
    roster_entries: list[FacultyEntry],
) -> list[dict[str, object]]:
    roster_names = {entry.normalized_name for entry in roster_entries}
    links: dict[str, dict[str, object]] = {}
    for page_url, html in page_cache.items():
        soup = BeautifulSoup(html, "html.parser")
        for anchor in soup.find_all("a", href=True):
            target = normalize_url(urljoin(page_url, anchor.get("href", "")))
            text = clean_text(anchor.get_text(" ", strip=True))
            if not target or not institution_related_domain(target, institution):
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


def discover_roster_profile_search_links(
    institution: Institution,
    roster_entries: list[FacultyEntry],
    country_code: str,
    disallowed_paths: list[str],
    existing_urls: Iterable[str],
    batch_queries: bool = False,
) -> tuple[list[dict[str, object]], list[str]]:
    search_hosts: list[str] = []
    seen_hosts: set[str] = set()
    for host in institution_search_hosts(institution):
        root = organization_root(host)
        if root and not (root in seen_hosts or seen_hosts.add(root)):
            search_hosts.append(root)

    del batch_queries  # Person-level verification must never trade recall for query batching.
    if not search_hosts:
        return [], []
    site_clause = (
        f"site:{search_hosts[0]}"
        if len(search_hosts) == 1
        else f"({' OR '.join(f'site:{host}' for host in search_hosts)})"
    )
    entries_by_intent: dict[str, list[FacultyEntry]] = {}
    existing = {normalize_url(url) for url in existing_urls}
    links: dict[str, dict[str, object]] = {}
    log: list[str] = []
    entries_with_urls: set[str] = set()

    def collect(searches: list[PlannedSearch]) -> None:
        for search, results in execute_search_round(
            searches,
            search_region_for_country(country_code),
        ):
            search_entries = entries_by_intent.get(search.intent, [])
            accepted = 0
            if search_entries:
                for result in results:
                    url = normalize_url(result.get("url", ""))
                    result_text = clean_text(
                        f'{result.get("title", "")} {result.get("body", "")} {url or ""}'
                    )
                    compact_result = re.sub(r"[^a-z0-9]+", "", fold_text(result_text))
                    matched_entries = []
                    for entry in search_entries:
                        name_parts = normalize_person_name(entry.name).split()
                        name_keys = {
                            re.sub(r"[^a-z0-9]+", "", fold_text(entry.name)),
                        }
                        if len(name_parts) >= 2:
                            name_keys.add(
                                re.sub(r"[^a-z0-9]+", "", f"{name_parts[0]}{name_parts[-1]}")
                            )
                        if any(len(key) >= 5 and key in compact_result for key in name_keys):
                            matched_entries.append(entry)
                    if (
                        not url
                        or url in existing
                        or not institution_related_domain(url, institution)
                        or not path_allowed(url, disallowed_paths)
                        or not matched_entries
                    ):
                        continue
                    matched_entry = max(matched_entries, key=lambda item: len(item.normalized_name))
                    links.setdefault(
                        url,
                        {
                            "url": url,
                            "text": matched_entry.name,
                            "score": 100,
                            "from": "person-level official-source audit",
                        },
                    )
                    entries_with_urls.add(matched_entry.normalized_name)
                    accepted += 1
            log.append(
                f"[person/{search.intent}] {search.query}: "
                f"{len(results)} result(s), {accepted} new official URL(s)"
            )

    primary_searches: list[PlannedSearch] = []
    for entry_index, entry in enumerate(roster_entries):
        intent = f"primary_{entry_index}"
        entries_by_intent[intent] = [entry]
        primary_searches.append(
            PlannedSearch(
                f'{site_clause} "{entry.name}" (email OR contact OR directory)',
                "person_audit",
                intent,
            )
        )
    collect(primary_searches)

    unresolved = [
        entry for entry in roster_entries if entry.normalized_name not in entries_with_urls
    ]
    expanded_searches: list[PlannedSearch] = []
    for entry_index, entry in enumerate(unresolved):
        intent = f"expanded_{entry_index}"
        entries_by_intent[intent] = [entry]
        expanded_searches.append(
            PlannedSearch(
                f'{site_clause} "{entry.name}" '
                "(faculty OR professor OR physician OR researcher OR directory)",
                "person_audit",
                intent,
            )
        )
    collect(expanded_searches)
    return sorted(links.values(), key=lambda item: str(item["url"])), log


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


def classify_institution_email(
    email: str,
    institution: Institution,
    allow_published_affiliate: bool = False,
) -> tuple[bool, str | None]:
    reasons: list[str] = []
    for official_host in institution_hosts(institution):
        accepted, reason = classify_email(
            email,
            official_host,
            allow_published_affiliate=allow_published_affiliate,
        )
        if accepted:
            return True, None
        if reason:
            reasons.append(reason)
    if reasons and all(reason == "Outside official domain family" for reason in reasons):
        return False, "Outside official domain family"
    return False, reasons[0] if reasons else "Outside official domain family"


def is_verified_evidence_page(source_url: str, institution: Institution) -> bool:
    source = normalize_url(source_url)
    if not source:
        return False
    evidence_urls = [institution.evidence_url, *institution.additional_evidence_urls]
    return any(
        evidence
        and source.rstrip("/") == evidence.rstrip("/")
        for evidence in (normalize_url(url) for url in evidence_urls)
    )


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

def labeled_profile_fields(soup: BeautifulSoup) -> dict[str, list[str]]:
    fields: dict[str, list[str]] = {}

    def add(label: str, value: str) -> None:
        key = fold_text(label).strip(" :|")
        cleaned = clean_text(value)
        if key and cleaned:
            fields.setdefault(key, []).append(cleaned)

    for row in soup.find_all("tr"):
        cells = row.find_all(["th", "td"], recursive=False)
        if len(cells) >= 2:
            add(cells[0].get_text(" ", strip=True), cells[1].get_text(" ", strip=True))
    for term in soup.find_all("dt"):
        value = term.find_next_sibling("dd")
        if value:
            add(term.get_text(" ", strip=True), value.get_text(" ", strip=True))
    return fields


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
    labeled_fields = labeled_profile_fields(soup)
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
    if not name:
        for label in ("name", "name of record", "full name"):
            for value in labeled_fields.get(label, []):
                candidate = clean_name(value)
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

    matched_entry = roster_by_name.get(normalize_person_name(name)) or next(
        (
            entry
            for entry in roster_entries
            if roster_name_match(name, {entry.normalized_name})
        ),
        None,
    )
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
        ok, reason = classify_institution_email(email, institution)
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
        ok, reason = classify_institution_email(email, institution)
        if ok:
            contacts.append(Contact(display_name, email, institution.name, profile_url, "Official public profile API", 0))
        elif reason:
            rejections.append(Rejection(display_name, reason, profile_url, email))
    if not contacts:
        rejections.append(Rejection(display_name, "No visible institutional email", profile_url))
    return contacts, rejections


def parse_public_directory_forms(
    hub_url: str,
    html: str,
    institution: Institution,
    disallowed_paths: list[str],
) -> list[dict[str, object]]:
    soup = BeautifulSoup(html, "html.parser")
    title = clean_text(soup.title.get_text(" ", strip=True) if soup.title else "")
    page_identity = fold_text(f"{hub_url} {title}")
    if "directory" not in page_identity:
        return []

    forms: list[dict[str, object]] = []
    seen: set[tuple[str, str, str]] = set()
    for form in soup.find_all("form"):
        method = clean_text(form.get("method") or "get").lower()
        if method not in {"get", "post"}:
            continue
        action_value = clean_text(form.get("action"))
        action_base = hub_url
        hub_path = urlparse(hub_url).path
        if (
            action_value
            and not urlparse(action_value).scheme
            and not action_value.startswith("/")
            and hub_path
            and not hub_path.endswith("/")
            and "." not in hub_path.rsplit("/", 1)[-1]
        ):
            action_base = f"{hub_url}/"
        action = normalize_url(urljoin(action_base, action_value or hub_url))
        if (
            not action
            or not institution_related_domain(action, institution)
            or not path_allowed(action, disallowed_paths)
            or any(marker in fold_text(action) for marker in ("login", "signin", "auth"))
        ):
            continue

        form_text = fold_text(form.get_text(" ", strip=True))
        radio_values = {
            clean_text(control.get("value")).casefold()
            for control in form.find_all("input")
            if clean_text(control.get("type")).casefold() == "radio"
        }
        person_search = "person" in form_text or "person" in radio_values
        if not person_search:
            continue

        query_inputs = [
            control
            for control in form.find_all("input")
            if control.get("name")
            and clean_text(control.get("type") or "text").casefold() in {"text", "search"}
        ]
        if not query_inputs:
            continue
        query_inputs.sort(
            key=lambda control: (
                clean_text(control.get("name")).casefold() not in {"query", "name", "keyword", "term"},
                clean_text(control.get("name")).casefold(),
            )
        )
        query_field = clean_text(query_inputs[0].get("name"))
        if not query_field:
            continue

        static_fields: dict[str, str] = {}
        radio_groups: dict[str, list[Tag]] = {}
        for control in form.find_all("input"):
            name = clean_text(control.get("name"))
            input_type = clean_text(control.get("type") or "text").casefold()
            if not name or name == query_field:
                continue
            if input_type == "hidden":
                static_fields[name] = clean_text(control.get("value"))
            elif input_type == "radio":
                radio_groups.setdefault(name, []).append(control)
            elif input_type == "submit" and name not in static_fields:
                static_fields[name] = clean_text(control.get("value"))
        for name, controls in radio_groups.items():
            chosen = next((control for control in controls if control.has_attr("checked")), None)
            chosen = chosen or next(
                (control for control in controls if clean_text(control.get("value")).casefold() == "person"),
                controls[0],
            )
            static_fields[name] = clean_text(chosen.get("value"))
        for select in form.find_all("select", attrs={"name": True}):
            options = select.find_all("option")
            if not options:
                continue
            chosen = next((option for option in options if option.has_attr("selected")), options[0])
            static_fields[clean_text(select.get("name"))] = clean_text(
                chosen.get("value") if chosen.get("value") is not None else chosen.get_text(" ", strip=True)
            )

        key = (method, action, query_field)
        if key in seen:
            continue
        seen.add(key)
        forms.append(
            {
                "hub_url": hub_url,
                "action": action,
                "method": method,
                "query_field": query_field,
                "static_fields": static_fields,
            }
        )
    return forms


def discover_public_directory_forms(
    page_cache: dict[str, str],
    institution: Institution,
    disallowed_paths: list[str],
) -> tuple[list[dict[str, object]], list[str]]:
    candidate_hubs: set[str] = set()
    for page_url, html in page_cache.items():
        soup = BeautifulSoup(html, "html.parser")
        if "directory" in fold_text(f"{page_url} {soup.title.get_text(' ', strip=True) if soup.title else ''}"):
            candidate_hubs.add(page_url)
        for anchor in soup.find_all("a", href=True):
            link = normalize_url(urljoin(page_url, anchor.get("href", "")))
            identity = fold_text(f"{link or ''} {anchor.get_text(' ', strip=True)}")
            if (
                link
                and "directory" in identity
                and institution_related_domain(link, institution)
                and path_allowed(link, disallowed_paths)
                and not any(marker in identity for marker in ("login", "signin", "intranet"))
            ):
                candidate_hubs.add(link)

    def inspect_hub(hub_url: str) -> tuple[list[dict[str, object]], str]:
        cached = page_cache.get(hub_url)
        html = cached
        final_url = hub_url
        if html is None:
            html, final_url, error = fetch_html(make_session(), hub_url)
            if not html or not final_url:
                return [], f"Directory candidate unavailable: {hub_url} ({error or 'unavailable'})"
        if not institution_related_domain(final_url, institution):
            return [], f"Directory candidate left the official domain: {hub_url}"
        forms = parse_public_directory_forms(final_url, html, institution, disallowed_paths)
        if forms:
            return forms, f"Verified public person directory: {final_url}"
        return [], f"Rejected non-person directory candidate: {final_url}"

    forms_by_key: dict[tuple[str, str, str, str], dict[str, object]] = {}
    log: list[str] = []
    with ThreadPoolExecutor(max_workers=min(6, len(candidate_hubs) or 1)) as executor:
        for found_forms, message in executor.map(inspect_hub, sorted(candidate_hubs)):
            log.append(message)
            for form in found_forms:
                action = str(form["action"])
                key = (
                    str(form["method"]),
                    organization_root(host_of(action)),
                    urlparse(action).path.rstrip("/").casefold(),
                    str(form["query_field"]),
                )
                forms_by_key.setdefault(key, form)
    return list(forms_by_key.values()), log


def directory_response_block_reason(page_text: str) -> str | None:
    folded = fold_text(page_text)
    markers = (
        ("viewed too many pages", "directory access threshold reached"),
        ("too many requests", "directory rate limited the request"),
        ("access denied", "directory denied access"),
        ("verify you are human", "directory requested human verification"),
        ("captcha", "directory requested human verification"),
    )
    for marker, reason in markers:
        if marker in folded:
            return reason
    return None


def matching_directory_record_soups(
    soup: BeautifulSoup,
    entry: FacultyEntry,
) -> list[BeautifulSoup]:
    roster_names = {entry.normalized_name}
    seeds: list[Tag] = []
    name_labels = {"name", "name of record", "full name", "display name"}
    for row in soup.find_all("tr"):
        cells = row.find_all(["th", "td"], recursive=False)
        if len(cells) >= 2 and fold_text(cells[0].get_text(" ", strip=True)).strip(" :|") in name_labels:
            if roster_name_match(cells[1].get_text(" ", strip=True), roster_names):
                seeds.append(cells[1])
    for term in soup.find_all("dt"):
        if fold_text(term.get_text(" ", strip=True)).strip(" :|") not in name_labels:
            continue
        value = term.find_next_sibling("dd")
        if value and roster_name_match(value.get_text(" ", strip=True), roster_names):
            seeds.append(value)
    for element in soup.find_all(
        ["h1", "h2", "h3", "h4", "td", "dd", "span", "strong", "b", "a"]
    ):
        text = clean_text(element.get_text(" ", strip=True))
        if len(text) <= 120 and roster_name_match(text, roster_names):
            seeds.append(element)

    records: dict[str, BeautifulSoup] = {}
    container_tags = {"article", "section", "li", "div", "table", "tbody", "main"}
    for seed in seeds:
        candidates: list[tuple[int, Tag]] = []
        for ancestor in [seed, *list(seed.parents)]:
            if not isinstance(ancestor, Tag) or ancestor.name in {"body", "html", "form"}:
                if isinstance(ancestor, Tag) and ancestor.name in {"body", "html"}:
                    break
                continue
            if ancestor.name not in container_tags:
                continue
            record_text = clean_text(ancestor.get_text(" ", strip=True))
            if len(record_text) > 12000:
                continue
            record_html = str(ancestor)
            if decode_visible_emails(record_html):
                candidates.append((len(record_text), ancestor))
        if candidates:
            _, container = min(candidates, key=lambda item: item[0])
            html = str(container)
            records.setdefault(html, BeautifulSoup(html, "html.parser"))

    if records:
        return list(records.values())

    page_text = clean_text(soup.get_text(" ", strip=True))
    if roster_name_match(page_text, roster_names) and decode_visible_emails(str(soup)):
        return [soup]
    return []


def parse_public_directory_response(
    final_url: str,
    html: str,
    institution: Institution,
    entry: FacultyEntry,
    terms: list[str],
) -> tuple[list[Contact], list[Rejection], str | None]:
    soup = BeautifulSoup(html, "html.parser")
    page_text = clean_text(soup.get_text(" ", strip=True))
    block_reason = directory_response_block_reason(page_text)
    if block_reason:
        return [], [], block_reason
    if "no matches found" in fold_text(page_text):
        return [], [], None

    contacts: list[Contact] = []
    rejections: list[Rejection] = []
    for record_soup in matching_directory_record_soups(soup, entry):
        response_fields = labeled_profile_fields(record_soup)
        department_text = clean_text(
            " ".join(
                value
                for label in ("department", "department name", "academic department", "unit")
                for value in response_fields.get(label, [])
            )
        )
        if department_text and not text_matches_terms(department_text, terms):
            rejections.append(
                Rejection(
                    entry.name,
                    "Directory record belongs to another department",
                    final_url,
                    department_text,
                )
            )
            continue
        found_contacts, found_rejections = parse_profile_page(
            final_url,
            str(record_soup),
            institution,
            [entry],
        )
        contacts.extend(found_contacts)
        rejections.extend(found_rejections)

    for contact in contacts:
        contact.method = "Official university directory"
        contact.profile_url = final_url
        contact.email_source_url = final_url
    return deduplicate_contacts(contacts), rejections, None


def crawl_public_directory_forms(
    forms: list[dict[str, object]],
    roster_entries: list[FacultyEntry],
    institution: Institution,
    terms: list[str],
    delay_seconds: float,
    disallowed_paths: list[str],
) -> tuple[list[Contact], list[Rejection], list[str], list[str]]:
    if not forms or not roster_entries:
        return [], [], [], []

    def lookup(payload: tuple[dict[str, object], FacultyEntry]) -> tuple[list[Contact], list[Rejection], str, str | None]:
        form, entry = payload
        hub_url = str(form["hub_url"])
        session = make_session()
        hub_html, hub_final_url, hub_error = fetch_html(session, hub_url)
        if not hub_html or not hub_final_url:
            return [], [], "", f"{hub_url}: {hub_error or 'directory unavailable'}"
        fresh_forms = parse_public_directory_forms(
            hub_final_url,
            hub_html,
            institution,
            disallowed_paths,
        )
        fresh_form = next(
            (
                candidate
                for candidate in fresh_forms
                if str(candidate["method"]) == str(form["method"])
                and str(candidate["query_field"]) == str(form["query_field"])
                and normalize_url(str(candidate["action"])) == normalize_url(str(form["action"]))
            ),
            form,
        )
        action = str(fresh_form["action"])
        method = str(fresh_form["method"])
        fields = dict(fresh_form.get("static_fields", {}))
        fields[str(fresh_form["query_field"])] = entry.name
        try:
            if method == "post":
                response = session.post(
                    action,
                    data=fields,
                    headers=HEADERS,
                    timeout=DEFAULT_TIMEOUT,
                    allow_redirects=True,
                )
            else:
                response = session.get(
                    action,
                    params=fields,
                    headers=HEADERS,
                    timeout=DEFAULT_TIMEOUT,
                    allow_redirects=True,
                )
            if response.status_code in {401, 403, 429}:
                return [], [], "", f"{action}: blocked or rate limited ({response.status_code})"
            response.raise_for_status()
        except requests.RequestException as exc:
            return [], [], "", f"{action}: {exc.__class__.__name__}"
        final_url = normalize_url(response.url)
        if not final_url or not institution_related_domain(final_url, institution):
            return [], [], "", None
        found_contacts, found_rejections, directory_block = parse_public_directory_response(
            final_url,
            response.text,
            institution,
            entry,
            terms,
        )
        if directory_block:
            return [], [], "", f"{action}: {directory_block}"
        if delay_seconds > 0:
            time.sleep(delay_seconds)
        return (
            found_contacts,
            found_rejections,
            f"{entry.name}: {len(found_contacts)} public directory contact(s)",
            None,
        )

    contacts: list[Contact] = []
    rejections: list[Rejection] = []
    log: list[str] = []
    blocked: list[str] = []
    for form in forms:
        for entry in roster_entries:
            found_contacts, found_rejections, message, blocked_message = lookup((form, entry))
            contacts.extend(found_contacts)
            rejections.extend(found_rejections)
            if message:
                log.append(message)
            if blocked_message:
                blocked.append(blocked_message)
                break
    return deduplicate_contacts(contacts), rejections, log, blocked


def crawl_profiles(
    profile_links: list[dict[str, object]],
    institution: Institution,
    roster_entries: list[FacultyEntry],
    delay_seconds: float,
    disallowed_paths: list[str],
) -> tuple[list[Contact], list[Rejection], list[str], list[str]]:
    contacts: list[Contact] = []
    rejections: list[Rejection] = []
    log: list[str] = []
    blocked: list[str] = []

    def inspect_profile(
        payload: tuple[int, dict[str, object]],
    ) -> tuple[list[Contact], list[Rejection], str, str | None]:
        index, link = payload
        url = str(link["url"])
        if not path_allowed(url, disallowed_paths):
            return [], [], f"Skipped by robots.txt: {url}", None
        session = make_session()
        html, final_url, error = fetch_html(session, url)
        if not html or not final_url:
            return [], [], "", f"{url}: {error or 'unavailable'}"
        if not institution_related_domain(final_url, institution):
            return [], [], "", None
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
                if delay_seconds > 0 and index < len(profile_links):
                    time.sleep(delay_seconds)
                return (
                    found_contacts,
                    found_rejections,
                    f"{final_url}: {len(found_contacts)} contact(s)",
                    f"{final_url}: {payload_error}",
                )
        if delay_seconds > 0 and index < len(profile_links):
            time.sleep(delay_seconds)
        return (
            found_contacts,
            found_rejections,
            f"{final_url}: {len(found_contacts)} contact(s)",
            None,
        )

    with ThreadPoolExecutor(max_workers=min(8, len(profile_links) or 1)) as executor:
        results = executor.map(inspect_profile, enumerate(profile_links, start=1))
        for found_contacts, found_rejections, message, blocked_message in results:
            contacts.extend(found_contacts)
            rejections.extend(found_rejections)
            if message:
                log.append(message)
            if blocked_message:
                blocked.append(blocked_message)
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
                ok, reason = classify_institution_email(
                    email,
                    institution,
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
                    ok, email_reason = classify_institution_email(
                        email,
                        institution,
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
    if not evidence_url or not institution_related_domain(evidence_url, institution):
        return [], [], False

    html, final_url, _ = fetch_html(make_session(), evidence_url)
    if not html or not final_url or not institution_related_domain(final_url, institution):
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
            ok, reason = classify_institution_email(
                email,
                institution,
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
        report.notes.append("Region-specific teaching page used as the authoritative contact source.")

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
    if department_pages:
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
    else:
        roster_entries = []
        faculty_pages = []
        role_rejections = []
        page_cache = dict(seed_cache)
        crawl_log = []
        blocked = []
        report.notes.append("Initial department discovery returned no qualifying page; completeness audit required.")
    report.faculty_roster_entries = len(roster_entries)
    report.pages_checked = len(crawl_log)
    report.blocked_or_unreadable.extend(blocked)
    report.rejections.extend(role_rejections)
    report.notes.extend(crawl_log[:8])

    update_activity("📄 Reviewing official documents...")
    pdf_contacts, pdf_rejections = extract_pdf_contacts(department_pages, institution, terms)
    report.rejections.extend(pdf_rejections)

    profile_contacts: list[Contact] = []
    profile_rejections: list[Rejection] = []
    profile_log: list[str] = []
    profile_blocked: list[str] = []
    if roster_entries:
        update_activity("🧭 Following relevant faculty links...")
        profile_links = discover_profile_links(page_cache, institution, roster_entries)
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

    initial_personal_contacts = deduplicate_contacts(
        evidence_contacts + profile_contacts + card_contacts + pdf_contacts
    )

    update_activity("🔍 Running independent completeness audit...")
    if len(initial_personal_contacts) < 5:
        report.notes.append(
            f"Low-result audit triggered after {len(initial_personal_contacts)} initial verified contact(s)."
        )
    audit_pages, audit_seed_cache, audit_log = discover_second_pass_pages(
        institution=institution,
        specialty=specialty,
        terms=terms,
        existing_urls={page.url for page in department_pages} | set(page_cache),
        disallowed_paths=disallowed_paths,
        country_code=country_code,
        compact=bool(roster_entries),
    )
    report.notes.extend(audit_log)
    report.department_pages += len(audit_pages)

    audit_profile_contacts: list[Contact] = []
    audit_card_contacts: list[Contact] = []
    audit_pdf_contacts: list[Contact] = []
    if audit_pages:
        audit_roster, audit_faculty_pages, audit_role_rejections, audit_page_cache, audit_crawl_log, audit_blocked = discover_faculty_roster(
            department_pages=audit_pages,
            institution=institution,
            terms=terms,
            delay_seconds=delay_seconds,
            disallowed_paths=disallowed_paths,
            seed_cache=audit_seed_cache,
        )
        audit_roster = filter_roster_to_location(
            audit_roster,
            country_code,
            region,
            region_code,
            region_kind,
        )
        existing_roster_names = {entry.normalized_name for entry in roster_entries}
        new_audit_roster = [
            entry for entry in audit_roster if entry.normalized_name not in existing_roster_names
        ]
        roster_entries.extend(new_audit_roster)
        page_cache.update(audit_page_cache)
        report.faculty_roster_entries = len(roster_entries)
        report.pages_checked += len(audit_crawl_log)
        report.blocked_or_unreadable.extend(audit_blocked)
        report.rejections.extend(audit_role_rejections)
        report.notes.extend(audit_crawl_log)

        audit_pdf_contacts, audit_pdf_rejections = extract_pdf_contacts(
            audit_pages,
            institution,
            terms,
        )
        report.rejections.extend(audit_pdf_rejections)

        audit_profile_links = discover_profile_links(
            audit_page_cache,
            institution,
            audit_roster,
        )
        audit_profile_contacts, audit_profile_rejections, audit_profile_log, audit_profile_blocked = crawl_profiles(
            profile_links=audit_profile_links,
            institution=institution,
            roster_entries=audit_roster,
            delay_seconds=delay_seconds,
            disallowed_paths=disallowed_paths,
        )
        report.profiles_checked += len(audit_profile_log)
        report.rejections.extend(audit_profile_rejections)
        report.blocked_or_unreadable.extend(audit_profile_blocked)
        report.notes.extend(audit_profile_log)

        audit_covered_names = {
            normalize_person_name(contact.name)
            for contact in initial_personal_contacts + audit_profile_contacts
        }
        audit_card_contacts, audit_card_rejections = extract_card_level_contacts(
            audit_roster,
            institution,
            audit_page_cache,
            audit_covered_names,
        )
        report.rejections.extend(audit_card_rejections)
        report.notes.append(
            f"Second-pass audit found {len(new_audit_roster)} new roster candidate(s) "
            f"across {len(audit_pages)} accepted page(s)."
        )
    else:
        report.notes.append("Second-pass audit found no new qualifying official pages.")

    contacts_before_directory = deduplicate_contacts(
        initial_personal_contacts
        + audit_profile_contacts
        + audit_card_contacts
        + audit_pdf_contacts
    )
    covered_before_directory = {
        normalize_person_name(contact.name)
        for contact in contacts_before_directory
    }
    directory_roster = [
        entry
        for entry in roster_entries
        if entry.normalized_name not in covered_before_directory
    ]
    directory_contacts: list[Contact] = []
    directory_forms: list[dict[str, object]] = []
    if directory_roster:
        update_activity("🔎 Checking official university directories...")
        directory_forms, directory_discovery_log = discover_public_directory_forms(
            page_cache,
            institution,
            disallowed_paths,
        )
        report.notes.extend(directory_discovery_log)
        if directory_forms:
            directory_contacts, directory_rejections, directory_log, directory_blocked = crawl_public_directory_forms(
                directory_forms,
                directory_roster,
                institution,
                terms,
                delay_seconds,
                disallowed_paths,
            )
            report.profiles_checked += len(directory_log) + len(directory_blocked)
            report.rejections.extend(directory_rejections)
            report.blocked_or_unreadable.extend(directory_blocked)
            report.notes.extend(directory_log)
            report.notes.append(
                f"Official directory audit verified {len(directory_contacts)} additional contact(s) "
                f"from {len(directory_roster)} unresolved roster candidate(s)."
            )

    contacts_before_person_search = deduplicate_contacts(
        contacts_before_directory + directory_contacts
    )
    covered_before_person_search = {
        normalize_person_name(contact.name)
        for contact in contacts_before_person_search
    }
    person_search_roster = [
        entry
        for entry in roster_entries
        if entry.normalized_name not in covered_before_person_search
    ]
    person_search_contacts: list[Contact] = []
    if person_search_roster:
        update_activity("🔎 Auditing each unresolved faculty member...")
        person_search_links, person_search_discovery_log = discover_roster_profile_search_links(
            institution,
            person_search_roster,
            country_code,
            disallowed_paths,
            set(page_cache)
            | {entry.profile_url for entry in roster_entries if entry.profile_url},
            batch_queries=False,
        )
        report.notes.extend(person_search_discovery_log)
        if person_search_links:
            person_search_contacts, person_search_rejections, person_search_log, person_search_blocked = crawl_profiles(
                person_search_links,
                institution,
                person_search_roster,
                delay_seconds,
                disallowed_paths,
            )
            report.profiles_checked += len(person_search_log)
            report.rejections.extend(person_search_rejections)
            report.blocked_or_unreadable.extend(person_search_blocked)
            report.notes.extend(person_search_log)
            report.notes.append(
                f"Person-level official-source audit verified {len(person_search_contacts)} additional contact(s) "
                f"for {len(person_search_roster)} unresolved roster candidate(s)."
            )

    update_activity(f"✨ Finishing {institution.name}...")
    personal_contacts = deduplicate_contacts(
        initial_personal_contacts
        + audit_profile_contacts
        + audit_card_contacts
        + audit_pdf_contacts
        + directory_contacts
        + person_search_contacts
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

st.set_page_config(
    page_title=APP_NAME,
    page_icon="GM",
    layout="wide",
    initial_sidebar_state="collapsed",
)

app_directory = Path(__file__).parent
watermark_paths = (
    app_directory / "assets" / "medical-technology-background.png",
    app_directory / "medical-technology-background.png",
)
watermark_path = next((path for path in watermark_paths if path.exists()), None)
if watermark_path:
    watermark_data = base64.b64encode(watermark_path.read_bytes()).decode("ascii")
    watermark_mime = "image/png"
else:
    watermark_data = EMBEDDED_BACKGROUND_WEBP
    watermark_mime = "image/webp"
watermark_url = f'data:{watermark_mime};base64,{watermark_data}'

st.markdown(
    f"""
    <style>
    .stApp {{ background: #11161c; }}
    header[data-testid="stHeader"] {{ background: rgba(17, 22, 28, 0.96); }}
    .stApp::before {{
        content: "";
        position: fixed;
        inset: 0;
        z-index: 0;
        pointer-events: none;
        background-image: url("{watermark_url}");
        background-position: right 1rem top 5rem;
        background-size: min(720px, 54vw) auto;
        background-repeat: no-repeat;
        filter: grayscale(0.72) saturate(0.45) brightness(0.72);
        opacity: 0.2;
        animation: medical-background-drift 24s ease-in-out infinite alternate;
    }}
    .stApp > * {{ position: relative; z-index: 1; }}
    @keyframes medical-background-drift {{
        from {{ transform: translate3d(0, 0, 0) scale(1); }}
        to {{ transform: translate3d(0.6rem, -0.3rem, 0) scale(1.018); }}
    }}
    @media (prefers-reduced-motion: reduce) {{
        .stApp::before {{ animation: none; }}
    }}
    .block-container {{ max-width: 1180px; padding-top: 1.5rem; }}
    div[data-testid="stVerticalBlockBorderWrapper"] {{
        background: rgba(17, 22, 28, 0.93);
        backdrop-filter: blur(7px);
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
        h1 {{
            font-size: 2.1rem !important;
            line-height: 1.14 !important;
            overflow-wrap: anywhere;
        }}
        .small-note {{
            font-size: 0.88rem;
            line-height: 1.4;
            overflow-wrap: anywhere;
        }}
        .stApp::before {{
            background-position: right -10rem top 6rem;
            background-size: auto 66vh;
            opacity: 0.12;
        }}
    }}
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

delay_seconds = DEFAULT_REQUEST_DELAY

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

        st.markdown("**Research audit log**")
        for report in reports:
            with st.expander(report.institution):
                st.code("\n".join(report.notes) or "No audit entries recorded.")

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

    if contacts:
        st.markdown("**Verified contact evidence**")
        st.dataframe(
            pd.DataFrame([
                {
                    "Name": contact.name,
                    "Email": contact.email,
                    "Institution": contact.institution,
                    "Profile URL": contact.profile_url,
                    "Email Source URL": contact.email_source_url,
                    "Evidence": contact.relevance_evidence,
                    "Confidence": contact.confidence,
                }
                for contact in contacts
            ]),
            use_container_width=True,
            hide_index=True,
        )

    if st.session_state.institution_log:
        st.markdown("**Institution discovery log**")
        st.code("\n".join(st.session_state.institution_log))


# ==================================================
# 16. CSV export
# ==================================================

# Export is handled by the Download CSV button above. The final DataFrame is
# always built by final_dataframe(), which returns exactly: Name, Email.
