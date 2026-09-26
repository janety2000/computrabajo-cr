import os
import re
import csv
import sys
import io
import json
import time
import base64
import hashlib
import logging
from datetime import datetime
from urllib.parse import urljoin, urlparse, parse_qs

import requests
from bs4 import BeautifulSoup

# ════════════════════════════════════════════════════════════════════════════
# CONFIG
# ════════════════════════════════════════════════════════════════════════════
BASE_URL = "https://cr.computrabajo.com"
HOME_URL = BASE_URL + "/"

REQUEST_TIMEOUT = 20
VERBOSE = True   # True = print every URL fetched, every job found, and every extracted field
PROCESSED_IDS_FILE = "cr_processed.csv"
PROGRESS_FILE = "cr_computrabajo_progress.json"   # {"location_index": int, "page": int}
SCRAPED_JOBS_CSV = "cr_scraped_jobs.csv"          # used when WP credentials aren't set
DONE_FLAG_FILE = "cr_SCRAPE_COMPLETE.flag"        # created once every location is exhausted

# ── Time budget (for GitHub Actions) ──────────────────────────────────────────
# A GH Actions job is killed hard at its timeout-minutes limit, mid-request,
# with no chance to save progress. So the script tracks its own elapsed time
# and stops itself gracefully (saving progress first) a safety margin before
# that happens. The workflow then commits progress and queues the next run.
# Default 300s (5 min) is only for quick local testing — the workflow always
# passes a real budget via the MAX_RUNTIME_SECONDS env var.
MAX_RUNTIME_SECONDS = int(os.environ.get("MAX_RUNTIME_SECONDS", "300"))
SCRIPT_START_TIME = time.time()


def time_budget_exceeded() -> bool:
    return (time.time() - SCRIPT_START_TIME) >= MAX_RUNTIME_SECONDS

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/96.0.4664.93 Safari/537.36"
    ),
    "Accept-Language": "es-CR,es;q=0.9,en;q=0.8",
    "Accept": "text/html,application/xhtml+xml",
}

# ── WordPress ─────────────────────────────────────────────────────────────────
# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  LOCAL / VS CODE / COLAB RUNS — PUT YOUR CREDENTIALS HERE                ║
# ║  Blank these back out before pushing to a public repo.                  ║
# ╚══════════════════════════════════════════════════════════════════════════╝
_LOCAL_WP_BASE_URL     = ""   # e.g. "https://yoursite.com/wp-json/wp/v2"
_LOCAL_WP_USERNAME     = ""   # e.g. "your-wp-username"
_LOCAL_WP_APP_PASSWORD = ""   # e.g. "abcd efgh ijkl mnop qrst uvwx"

WP_URL      = _LOCAL_WP_BASE_URL or os.environ.get("WP_BASE_URL", "")
WP_USER     = _LOCAL_WP_USERNAME or os.environ.get("WP_USERNAME", "")
WP_PASSWORD = _LOCAL_WP_APP_PASSWORD or os.environ.get("WP_APP_PASSWORD", "")

WP_BASE        = WP_URL.rstrip("/")
WP_JOBS_URL    = f"{WP_BASE}/job-listings"
WP_COMPANY_URL = f"{WP_BASE}/companies"
WP_MEDIA_URL   = f"{WP_BASE}/media"

JOB_TYPE_MAPPING = {
    "full_time": "full-time", "full-time": "full-time", "fulltime": "full-time",
    "part_time": "part-time", "part-time": "part-time", "parttime": "part-time",
    "contractor": "contract", "contract": "contract",
    "temporary": "temporary", "temp": "temporary",
    "intern": "internship", "internship": "internship",
    "volunteer": "volunteer",
    "per_diem": "contract", "other": "full-time",
}

# ── Logging (Colab-safe) ──────────────────────────────────────────────────────
logger = logging.getLogger()
logger.setLevel(logging.DEBUG)
logger.handlers.clear()

_fh = logging.FileHandler("debug.log", encoding="utf-8")
_fh.setLevel(logging.DEBUG)
_fh.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))
logger.addHandler(_fh)

try:
    # Colab / some Jupyter kernels replace sys.stdout with an object that has
    # no .buffer attribute, which crashes io.TextIOWrapper(sys.stdout.buffer, ...)
    _utf8_stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")
except AttributeError:
    _utf8_stdout = sys.stdout

_ch = logging.StreamHandler(_utf8_stdout)
_ch.setLevel(logging.DEBUG if VERBOSE else logging.INFO)
_ch.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))
logger.addHandler(_ch)


def require_wp_config() -> bool:
    """Returns True if WP posting is fully configured, False otherwise.
    No longer raises — the script runs fine without WordPress creds by
    falling back to writing everything into scraped_jobs.csv instead."""
    missing = [n for n, v in
               [("WP_BASE_URL", WP_URL), ("WP_USERNAME", WP_USER), ("WP_APP_PASSWORD", WP_PASSWORD)]
               if not v]
    if missing:
        logger.warning(
            f"⚠️  WordPress credentials not set ({', '.join(missing)}) — "
            f"WP posting is DISABLED. Scraped jobs will be written to {SCRAPED_JOBS_CSV} instead. "
            f"Fill in the _LOCAL_WP_* variables near the top of this file to enable posting."
        )
        return False
    return True


# ════════════════════════════════════════════════════════════════════════════
# HTTP SESSION
# ════════════════════════════════════════════════════════════════════════════
SESSION = requests.Session()
SESSION.headers.update(HEADERS)


def wp_headers() -> dict:
    token = base64.b64encode(f"{WP_USER}:{WP_PASSWORD}".encode()).decode()
    return {"Authorization": f"Basic {token}", "Content-Type": "application/json"}


def get_soup(url: str, timeout: int = REQUEST_TIMEOUT) -> BeautifulSoup:
    resp = SESSION.get(url, timeout=timeout)
    resp.encoding = "utf-8"
    logger.debug(f"    GET {url} → HTTP {resp.status_code} ({len(resp.text):,} chars)")
    return BeautifulSoup(resp.text, "html.parser")


# ════════════════════════════════════════════════════════════════════════════
# SANITIZATION
# ════════════════════════════════════════════════════════════════════════════
def sanitize(value) -> str:
    if value is None:
        return ""
    if not isinstance(value, str):
        value = str(value)
    text = re.sub(r"<[^>]+>", " ", value)          # strip any leftover HTML tags
    text = re.sub(r"[\x00-\x08\x0B\x0C\x0E-\x1F\x7F]", "", text)
    text = re.sub(r"[ \t]+", " ", text)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.strip()


def normalise_job_type(raw: str) -> str:
    return JOB_TYPE_MAPPING.get((raw or "").lower().strip(), "full-time")


def add_three_months(posted_date: datetime) -> str:
    month = posted_date.month - 1 + 3
    year = posted_date.year + month // 12
    month = month % 12 + 1
    day = min(posted_date.day, 28)
    return datetime(year, month, day).strftime("%Y-%m-%d")


def make_job_id(job_url: str) -> str:
    return hashlib.md5(job_url.encode()).hexdigest()[:16]


# ════════════════════════════════════════════════════════════════════════════
# DEDUP TRACKER
# ════════════════════════════════════════════════════════════════════════════
def _init_tracker():
    if not os.path.exists(PROCESSED_IDS_FILE):
        with open(PROCESSED_IDS_FILE, "w", newline="", encoding="utf-8") as f:
            csv.writer(f).writerow(
                ["Job ID", "Job URL", "Job Title", "Status", "Timestamp", "Location", "Page"]
            )


def load_processed_ids() -> set:
    _init_tracker()
    with open(PROCESSED_IDS_FILE, newline="", encoding="utf-8") as f:
        return {row["Job ID"] for row in csv.DictReader(f)}


def mark_processed(job_id: str, job_url: str, title: str, status: str,
                    location=None, page_num=None):
    _init_tracker()
    with open(PROCESSED_IDS_FILE, "a", newline="", encoding="utf-8") as f:
        csv.writer(f).writerow([
            job_id, job_url, title, status, datetime.now().isoformat(),
            location or "", page_num if page_num is not None else "",
        ])


# ════════════════════════════════════════════════════════════════════════════
# PROGRESS TRACKER (resumable across locations + pages)
# ════════════════════════════════════════════════════════════════════════════
def load_progress() -> dict:
    if os.path.exists(PROGRESS_FILE):
        try:
            with open(PROGRESS_FILE, encoding="utf-8") as f:
                return json.load(f)
        except (ValueError, OSError):
            pass
    return {"location_index": 0, "page": 1}


def save_progress(location_index: int, page: int):
    with open(PROGRESS_FILE, "w", encoding="utf-8") as f:
        json.dump({"location_index": location_index, "page": page}, f)


_CSV_FIELDS = [
    "job_title", "job_type", "job_qualifications", "job_experience", "job_location",
    "job_field", "date_posted", "deadline", "job_description", "application",
    "company_url", "company_name", "company_logo", "company_industry", "company_founded",
    "company_type", "company_website", "company_address", "company_details", "job_url",
    "estimated_deadline", "salary_range", "external_id",
]


def _init_scraped_jobs_csv():
    if not os.path.exists(SCRAPED_JOBS_CSV):
        with open(SCRAPED_JOBS_CSV, "w", newline="", encoding="utf-8") as f:
            csv.DictWriter(f, fieldnames=_CSV_FIELDS).writeheader()


def save_job_to_csv(job: dict):
    _init_scraped_jobs_csv()
    with open(SCRAPED_JOBS_CSV, "a", newline="", encoding="utf-8") as f:
        csv.DictWriter(f, fieldnames=_CSV_FIELDS).writerow(
            {k: job.get(k, "") for k in _CSV_FIELDS}
        )


# ════════════════════════════════════════════════════════════════════════════
# STEP 1 — DISCOVER LOCATIONS FROM THE HOMEPAGE
# ════════════════════════════════════════════════════════════════════════════
def get_location_urls() -> list:
    """
    Scrapes the "Bolsa de empleo según: Localidad" block on the Costa Rica
    homepage, which lists department links (e.g. /empleos-en-antioquia) and
    their main cities (e.g. /empleos-en-medellin). Returns full URLs,
    de-duplicated and in the order they appear on the page.
    """
    logger.info(f"Fetching homepage: {HOME_URL}")
    soup = get_soup(HOME_URL)

    container = soup.select_one("div.lL")
    if not container:
        logger.warning("Could not find the location block (div.lL) on the homepage.")
        return []

    seen = set()
    urls = []
    for a in container.select("ul#content_1 a[href]"):
        href = a.get("href", "").strip()
        if not href or href.startswith("http") and BASE_URL not in href:
            continue
        full = urljoin(BASE_URL, href)
        if full not in seen:
            seen.add(full)
            urls.append(full)

    logger.info(f"📍 Found {len(urls)} location URLs on the homepage.")
    for i, u in enumerate(urls):
        logger.debug(f"    [{i}] {u}")
    return urls


# ════════════════════════════════════════════════════════════════════════════
# STEP 2 — PAGINATE A LOCATION'S JOB LISTING GRID
# ════════════════════════════════════════════════════════════════════════════
def build_page_url(location_url: str, page_num: int) -> str:
    if page_num <= 1:
        return location_url
    sep = "&" if "?" in location_url else "?"
    return f"{location_url}{sep}p={page_num}"


def scrape_job_list_page(location_url: str, page_num: int) -> list:
    url = build_page_url(location_url, page_num)
    logger.info(f"Fetching listing page {page_num}: {url}")
    try:
        soup = get_soup(url)
    except Exception as e:
        logger.error(f"Error fetching {url}: {e}")
        return []

    urls = []
    for article in soup.select("article.box_offer"):
        a = article.select_one("h2 a.js-o-link[href]")
        if not a:
            continue
        href = a["href"].split("#")[0]   # strip the #lc=... tracking fragment
        urls.append(urljoin(BASE_URL, href))

    logger.info(f"Found {len(urls)} job URLs on page {page_num}")
    for i, u in enumerate(urls, start=1):
        logger.debug(f"    job {i}: {u}")
    return urls


# ════════════════════════════════════════════════════════════════════════════
# STEP 3 — EXTRACT JOB DETAILS (JSON-LD first, HTML fallback)
# ════════════════════════════════════════════════════════════════════════════
def _find_jobposting_jsonld(soup: BeautifulSoup) -> dict:
    for script in soup.select('script[type="application/ld+json"]'):
        raw = script.string or script.get_text()
        if not raw or "JobPosting" not in raw:
            continue
        try:
            data = json.loads(raw)
        except (ValueError, TypeError):
            continue
        candidates = data.get("@graph", [data]) if isinstance(data, dict) else data
        if not isinstance(candidates, list):
            candidates = [candidates]
        for entry in candidates:
            if isinstance(entry, dict) and entry.get("@type") == "JobPosting":
                return entry
    return {}


def _html_fallback_fields(soup: BeautifulSoup) -> dict:
    """Used only if the JobPosting JSON-LD block is missing/unparsable."""
    title_el = soup.select_one("h1.fwB.fs24")
    title = title_el.get_text(strip=True) if title_el else ""

    desc_el = soup.select_one('div[div-link="oferta"] p.mbB')
    description = desc_el.get_text(" ", strip=True) if desc_el else ""

    company_loc_el = soup.select_one("main p.fs16")
    company, location = "", ""
    if company_loc_el:
        parts = company_loc_el.get_text(strip=True).split(" - ")
        if len(parts) == 2:
            company, location = parts

    salary_el = soup.select_one('div[div-link="oferta"] span.tag.base')
    salary = salary_el.get_text(strip=True) if salary_el else ""

    return {
        "title": title,
        "description": description,
        "hiringOrganization": {"name": company},
        "jobLocation": {"address": {"addressLocality": location}},
        "baseSalary": {"value": {"value": salary}} if salary else {},
        "datePosted": "",
        "validThrough": "",
        "employmentType": "",
        "industry": "",
    }


def scrape_job_details(job_url: str) -> dict:
    soup = get_soup(job_url)
    jp = _find_jobposting_jsonld(soup)
    if not jp:
        logger.warning(f"No JobPosting JSON-LD found, using HTML fallback: {job_url}")
        jp = _html_fallback_fields(soup)
        if not jp.get("title"):
            logger.warning(f"Fallback extraction failed — skipping: {job_url}")
            return {}

    title = jp.get("title", "")
    description = jp.get("description", "")
    if not title or not description:
        logger.warning(f"Missing title/description — skipping: {job_url}")
        return {}

    org = jp.get("hiringOrganization") or {}
    company_name = org.get("name", "")
    company_logo = org.get("logo", "")

    loc = (jp.get("jobLocation") or {}).get("address") or {}
    # Computrabajo's schema puts the city in addressRegion and department in
    # addressLocality on some pages (it's inconsistent) — combine both.
    location_parts = [p for p in (loc.get("addressRegion"), loc.get("addressLocality")) if p]
    job_location = ", ".join(dict.fromkeys(location_parts))  # de-dup, keep order

    salary_val = ((jp.get("baseSalary") or {}).get("value") or {})
    salary_amount = salary_val.get("value", "")
    salary_currency = jp.get("salaryCurrency", "CRC")
    salary_range = f"{salary_amount} {salary_currency}".strip() if salary_amount else ""

    date_posted_str = jp.get("datePosted", "")
    date_posted = None
    for fmt in ("%Y-%m-%d", "%Y-%m-%dT%H:%M:%S"):
        try:
            date_posted = datetime.strptime(date_posted_str[:19], fmt)
            break
        except (ValueError, TypeError):
            continue

    estimated_deadline = add_three_months(date_posted) if date_posted else ""
    deadline = jp.get("validThrough", "") or estimated_deadline

    job_type = normalise_job_type(jp.get("employmentType", ""))
    identifier = (jp.get("identifier") or {}).get("value", "") if isinstance(jp.get("identifier"), dict) else ""

    job = {
        "job_title": sanitize(title),
        "job_type": sanitize(job_type),
        "job_qualifications": "",     # not reliably present in Computrabajo's schema
        "job_experience": "",
        "job_location": sanitize(job_location) or "Costa Rica",
        "job_field": sanitize(jp.get("industry", "")),
        "date_posted": sanitize(date_posted_str),
        "deadline": sanitize(deadline),
        "job_description": sanitize(description),
        "application": sanitize(job_url),   # Computrabajo apply flow requires login; store source link
        "company_url": "",
        "company_name": sanitize(company_name),
        "company_logo": sanitize(company_logo),
        "company_industry": sanitize(jp.get("industry", "")),
        "company_founded": "",
        "company_type": "",
        "company_website": "",
        "company_address": sanitize(job_location),
        "company_details": "",
        "job_url": sanitize(job_url),
        "estimated_deadline": sanitize(estimated_deadline),
        "salary_range": sanitize(salary_range),
        "external_id": sanitize(identifier),
    }

    log_scraped_job(job_url, job)
    return job


def log_scraped_job(job_url: str, job: dict):
    """Prints every extracted field for a job — the core of VERBOSE mode."""
    desc_preview = (job["job_description"][:200] + "…") if len(job["job_description"]) > 200 else job["job_description"]
    logger.info(
        "    ┌─ SCRAPED JOB ─────────────────────────────────────────\n"
        f"    │ URL          : {job_url}\n"
        f"    │ Title        : {job['job_title']}\n"
        f"    │ Company      : {job['company_name'] or '(none)'}\n"
        f"    │ Location     : {job['job_location']}\n"
        f"    │ Job type     : {job['job_type']}\n"
        f"    │ Salary       : {job['salary_range'] or '(not listed)'}\n"
        f"    │ Industry     : {job['job_field'] or '(none)'}\n"
        f"    │ Date posted  : {job['date_posted'] or '(unknown)'}\n"
        f"    │ Deadline     : {job['deadline'] or '(estimated: ' + job['estimated_deadline'] + ')'}\n"
        f"    │ External ID  : {job['external_id'] or '(none)'}\n"
        f"    │ Description  : {desc_preview}\n"
        "    └───────────────────────────────────────────────────────"
    )


# ════════════════════════════════════════════════════════════════════════════
# WORDPRESS (same pattern as the MyJobMag scraper)
# ════════════════════════════════════════════════════════════════════════════
def upload_logo(logo_url: str):
    if not logo_url or not logo_url.startswith("http"):
        return None
    ext = logo_url.lower().rsplit(".", 1)[-1].split("?")[0]
    if ext not in ("png", "jpg", "jpeg", "webp"):
        return None
    try:
        img = SESSION.get(logo_url, timeout=15)
        img.raise_for_status()
        headers = wp_headers()
        headers["Content-Disposition"] = f"attachment; filename={logo_url.split('/')[-1].split('?')[0]}"
        headers["Content-Type"] = img.headers.get("content-type", "image/jpeg")
        r = SESSION.post(WP_MEDIA_URL, headers=headers, data=img.content,
                          auth=(WP_USER, WP_PASSWORD), timeout=20)
        r.raise_for_status()
        return r.json().get("id")
    except Exception as e:
        logger.error(f"Logo upload error: {e}")
        return None


_term_cache = {}


def get_or_create_term(taxonomy_url: str, name: str):
    if not name or not name.strip():
        return None
    slug = re.sub(r"[^a-z0-9-]", "-", name.lower().strip())
    cache_key = (taxonomy_url, slug)
    if cache_key in _term_cache:
        return _term_cache[cache_key]
    try:
        r = SESSION.get(f"{taxonomy_url}?slug={slug}", headers=wp_headers(), timeout=10)
        terms = r.json()
        if isinstance(terms, list) and terms:
            _term_cache[cache_key] = terms[0]["id"]
            return terms[0]["id"]
    except Exception:
        pass
    try:
        r = SESSION.post(taxonomy_url, json={"name": name, "slug": slug},
                          headers=wp_headers(), auth=(WP_USER, WP_PASSWORD), timeout=10)
        term_id = r.json().get("id")
        _term_cache[cache_key] = term_id
        return term_id
    except Exception as e:
        logger.error(f"Term create error '{name}': {e}")
        return None


def ensure_job_type_terms():
    for jt_label in ["Full Time", "Part Time", "Contract", "Temporary", "Internship", "Volunteer"]:
        get_or_create_term(f"{WP_BASE}/job_listing_type", jt_label)


def save_company(job: dict):
    name = job["company_name"]
    if not name:
        return None
    slug = re.sub(r"[^a-z0-9-]", "-", name.lower())
    try:
        r = SESSION.get(f"{WP_COMPANY_URL}?slug={slug}", headers=wp_headers(), timeout=10)
        posts = r.json()
        if isinstance(posts, list) and posts:
            logger.info(f"⏭ Company exists: {name}")
            return posts[0]["id"]
    except Exception:
        pass

    attachment_id = upload_logo(job["company_logo"])
    payload = {
        "title": name,
        "content": job["company_details"],
        "status": "publish",
        "featured_media": attachment_id or 0,
        "meta": {
            "_company_name": name,
            "_company_logo": str(attachment_id) if attachment_id else "",
            "_company_industry": job["company_industry"],
            "_company_website": job["company_website"],
        },
    }
    try:
        r = SESSION.post(WP_COMPANY_URL, json=payload, headers=wp_headers(),
                          auth=(WP_USER, WP_PASSWORD), timeout=20)
        r.raise_for_status()
        post = r.json()
        logger.info(f"✅ Company posted: {name} → ID {post.get('id')}")
        return post.get("id")
    except Exception as e:
        logger.error(f"Company post error '{name}': {e}")
        return None


def save_job(job: dict):
    title       = job["job_title"]
    description = job["job_description"]
    location    = job["job_location"] or "Costa Rica"
    job_type_s  = job["job_type"] or "full-time"
    company     = job["company_name"]
    deadline    = job["deadline"] or job["estimated_deadline"]

    slug = re.sub(r"[^a-z0-9-]", "-", title.lower())[:80]
    try:
        r = SESSION.get(f"{WP_JOBS_URL}?slug={slug}", headers=wp_headers(), timeout=10)
        posts = r.json()
        if isinstance(posts, list) and posts:
            logger.info(f"⏭ Job already on WP: {title}")
            return posts[0]["id"], posts[0].get("link")
    except Exception:
        pass

    attachment_id    = upload_logo(job["company_logo"])
    region_term_id   = get_or_create_term(f"{WP_BASE}/job_listing_region", location)
    job_type_term_id = get_or_create_term(f"{WP_BASE}/job_listing_type", job_type_s.replace("-", " ").title())

    payload = {
        "title": title,
        "content": description,
        "status": "publish",
        "featured_media": attachment_id or 0,
        "meta": {
            "_job_title":          title,
            "_job_location":       location,
            "_job_type":           job_type_s,
            "_job_description":    description,
            "_application":        job["application"],
            "_job_expires":        deadline,
            "_company_name":       company,
            "_company_website":    job["company_website"],
            "_company_logo":       str(attachment_id) if attachment_id else "",
            "_company_industry":   job["company_industry"],
            "_company_address":    job["company_address"],
            "_job_qualifications": job["job_qualifications"],
            "_job_experiences":    job["job_experience"],
            "_job_field":          job["job_field"],
            "_job_source_url":     job["job_url"],
            "_job_salary":         job["salary_range"],
            "_external_id":        job["external_id"],
        },
    }
    if region_term_id:
        payload["job_listing_region"] = [region_term_id]
    if job_type_term_id:
        payload["job_listing_type"] = [job_type_term_id]

    for attempt in range(3):
        try:
            r = SESSION.post(WP_JOBS_URL, json=payload, headers=wp_headers(),
                              auth=(WP_USER, WP_PASSWORD), timeout=25)
            r.raise_for_status()
            post = r.json()
            logger.info(f"✅ Job posted: '{title}' → WP ID {post.get('id')}")
            return post.get("id"), post.get("link")
        except Exception as e:
            logger.error(f"Job post attempt {attempt + 1} failed: {e}")
            if attempt < 2:
                time.sleep(2 ** attempt)
    return None, None


# ════════════════════════════════════════════════════════════════════════════
# MAIN
# ════════════════════════════════════════════════════════════════════════════
class _TimeBudgetExceeded(Exception):
    """Raised internally to unwind cleanly once MAX_RUNTIME_SECONDS is hit."""
    pass


def run():
    if os.path.exists(DONE_FLAG_FILE):
        logger.info(f"🏁 {DONE_FLAG_FILE} already exists — all locations were fully scraped on a "
                    f"previous run. Delete this file if you want to force a fresh full re-scrape.")
        return

    wp_enabled = require_wp_config()
    if wp_enabled:
        ensure_job_type_terms()
    processed_ids = load_processed_ids()
    logger.info(f"📋 {len(processed_ids)} jobs already in tracker.")

    locations = get_location_urls()
    if not locations:
        logger.error("No locations found — aborting.")
        return

    progress = load_progress()
    start_loc_idx = min(progress.get("location_index", 0), len(locations) - 1)
    start_page = progress.get("page", 1)

    posted = skipped = failed = 0

    logger.info(f"🚀 Starting Computrabajo Costa Rica scrape across {len(locations)} locations, "
                f"resuming at location #{start_loc_idx} ({locations[start_loc_idx]}), page {start_page}.")

    try:
        for loc_idx in range(start_loc_idx, len(locations)):
            location_url = locations[loc_idx]
            page_num = start_page if loc_idx == start_loc_idx else 1

            while True:
                job_urls = scrape_job_list_page(location_url, page_num)
                if not job_urls:
                    logger.info(f"📄 No more jobs at {location_url} (page {page_num}) — moving to next location.")
                    break

                for j, job_url in enumerate(job_urls, start=1):
                    logger.info(f"── {location_url} | page {page_num} | job {j}/{len(job_urls)}: {job_url}")

                    job_id = make_job_id(job_url)
                    if job_id in processed_ids:
                        logger.info("⏭ SKIP (pre-check) — already processed.")
                        skipped += 1
                        continue

                    try:
                        job = scrape_job_details(job_url)
                    except Exception as e:
                        logger.error(f"Error scraping job {job_url}: {e}")
                        failed += 1
                        continue

                    if not job:
                        mark_processed(job_id, job_url, "", "skipped_incomplete", location_url, page_num)
                        processed_ids.add(job_id)
                        skipped += 1
                        continue

                    if job["company_name"]:
                        if wp_enabled:
                            save_company(job)

                    if wp_enabled:
                        post_id, post_url = save_job(job)
                        if post_id:
                            mark_processed(job_id, job_url, job["job_title"],
                                            f"posted|wp_id={post_id}|{post_url or ''}", location_url, page_num)
                            posted += 1
                            logger.info(f"✅ SUCCESS — '{job['job_title']}' → WP ID={post_id} 🔗 {post_url}")
                        else:
                            mark_processed(job_id, job_url, job["job_title"], "wp_post_failed", location_url, page_num)
                            failed += 1
                            logger.info(f"❌ WordPress post failed: {job['job_title']}")
                    else:
                        save_job_to_csv(job)
                        mark_processed(job_id, job_url, job["job_title"], "saved_to_csv", location_url, page_num)
                        posted += 1
                        logger.info(f"✅ SAVED — '{job['job_title']}' → {SCRAPED_JOBS_CSV}")

                    processed_ids.add(job_id)
                    time.sleep(1)   # be polite to the source site

                    if time_budget_exceeded():
                        # Save progress as this exact page (it's not finished yet,
                        # so re-fetching it next run is correct — already-processed
                        # jobs on it will just hit the dedup skip instantly).
                        save_progress(loc_idx, page_num)
                        raise _TimeBudgetExceeded()

                save_progress(loc_idx, page_num + 1)
                logger.info(f"📊 Running totals — posted: {posted} | skipped: {skipped} | failed: {failed}")
                page_num += 1

            # finished this location entirely — next location starts at page 1
            save_progress(loc_idx + 1, 1)

        logger.info(f"\n{'#'*60}")
        logger.info(f" ✅ FINISHED all {len(locations)} locations ({datetime.now().strftime('%Y-%m-%d %H:%M')})")
        logger.info(f" ✅ Posted  : {posted}")
        logger.info(f" ⏭ Skipped : {skipped}")
        logger.info(f" ❌ Failed  : {failed}")
        if not wp_enabled:
            logger.info(f" 📄 Output  : {SCRAPED_JOBS_CSV}")
        logger.info(f"{'#'*60}")
        # Tell the GitHub Actions workflow there's nothing left to resume —
        # it checks for this file and stops re-triggering itself once it exists.
        with open(DONE_FLAG_FILE, "w", encoding="utf-8") as f:
            f.write(f"All {len(locations)} locations fully scraped as of "
                     f"{datetime.now().isoformat()}. Delete this file to force a fresh full re-scrape.")

    except _TimeBudgetExceeded:
        elapsed = time.time() - SCRIPT_START_TIME
        logger.info(f"\n{'#'*60}")
        logger.info(f" ⏱ TIME BUDGET REACHED after {elapsed:.0f}s "
                    f"(limit {MAX_RUNTIME_SECONDS}s) — stopping cleanly.")
        logger.info(f" ▶️  Progress saved. The workflow will queue the next run automatically.")
        logger.info(f" ✅ Posted  : {posted}")
        logger.info(f" ⏭ Skipped : {skipped}")
        logger.info(f" ❌ Failed  : {failed}")
        logger.info(f"{'#'*60}")

    except KeyboardInterrupt:
        logger.info(f"\n{'#'*60}")
        logger.info(f" STOPPED BY USER ({datetime.now().strftime('%Y-%m-%d %H:%M')})")
        logger.info(f" ▶️  Re-run the script to resume from where it left off.")
        logger.info(f" ✅ Posted  : {posted}")
        logger.info(f" ⏭ Skipped : {skipped}")
        logger.info(f" ❌ Failed  : {failed}")
        logger.info(f"{'#'*60}")


if __name__ == "__main__":
    logger.info("🚀 Computrabajo Costa Rica scraper — starting… (Ctrl+C to stop, safe to resume)")
    run()
    logger.info("✅ Done.")
