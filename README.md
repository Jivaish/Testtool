# Global Medical Faculty Contact Finder

A ready-to-deploy Streamlit app for building complete faculty rosters and enriching them with publicly visible official work emails and phone numbers from universities, colleges, medical schools, teaching hospitals, health-science institutions, and academic centres.

The app first discovers verified institutions and displays their official website links.
The default workflow lets the user paste one or more exact department faculty-page URLs
for each institution; the app then renders dynamic directories, follows pagination and
lazy-loaded results to their natural end, extracts the roster, follows linked official profiles,
verifies published emails and phones, reconciles every person back to the roster, and organizes the output. Faculty remain in the result when an email or phone is not published. An
automatic website-search mode remains available as a secondary option.

Public web discovery uses a pluggable search-provider layer backed by DDGS in automatic
backend mode. It uses localized search regions when available and a global search region
everywhere else. No paid AI or Google API is required.

The deterministic query planner works in evidence-driven rounds. It first explores
institution identities and specialty matches, then searches unresolved official domains
for faculty, department, curriculum, clerkship, clinical-training, contact, and document
evidence. Extended searches stop only when the current evidence gaps have converged;
there is no result-count cap. Candidates must then pass official-site brand, location,
and specialty-evidence checks. Search snippets help discovery but never serve as the
final authority for an institution or contact.

Institution results are canonicalized by verified organization identity, so multiple
subdomains and alternate result titles do not create repeated institutions. Generic
facility labels and residency-program titles are not treated as universities or medical
schools. Parent-owned centers, libraries, health systems, and academic hospital domains
are retained as additional official evidence sources without becoming duplicate choices.
An institution is accepted only when official content proves a relevant academic unit,
academic program, or required medical-training relationship; a clinical service or course
mention alone is insufficient. When a strong official academic candidate lacks specialty
evidence in the first result set, the app performs targeted faculty, curriculum, and
training follow-ups restricted to that institution's own domain.

Country selection uses the full ISO country list. The location dropdown combines official country subdivisions with searchable city data, and includes an all-regions option.

## Output

The final table and downloadable CSV are roster-first. Contact fields remain blank when they are not publicly published:

```text
Name,Title,Email,Phone,Profile,Institution,Department,Directory URL,
Name Source URL,Email Source URL,Phone Source URL,Profile Status,
Email Status,Phone Status
```

Each person has one reconciled faculty record. Duplicate directory or profile appearances are merged by institution, normalized name, and profile identity; two different people who share a name are not merged when their profile URLs differ. Generic department fallback emails are never assigned to faculty members.

## Accuracy Rule

Accuracy means both roster completeness and contact provenance:

- the person is associated with the selected department or a directly related academic unit,
- every valid person on a user-supplied authoritative faculty directory is retained, even when title, email, or phone is unavailable,
- automatic discovery requires faculty, academic teaching staff, or eligible academic-research evidence,
- any email is visibly published on an official institutional teaching source,
- the email is an institutional work email, or a professional affiliate email explicitly
  published beside the faculty member on that verified teaching source,
- the name and contact fields are locally associated on a profile, card, directory row, official PDF, or similar source,
- any phone number is taken only from the same local person card or profile,
- directory, name, email, phone, profile, and extraction-status provenance remain available in diagnostics and CSV output.

The app never guesses, generates, constructs, infers, or predicts emails from names.

For every selected institution, the crawler expands the specialty into related academic
units, classifies official pages, builds an authoritative or evidence-filtered roster, visits every discovered
profile, verifies displayed contact evidence, reconciles the enriched records, and runs an
independent second-pass audit. A low initial yield triggers the same broader audit rather
than an early zero-result conclusion. Diagnostics retain discovered URLs, page
classification, acceptance/rejection reasons, directory counts, unique-faculty counts,
profile attempts/successes/failures, with/without-email and with/without-phone counts,
duplicate merges, missing people, field source URLs, relevance evidence, and confidence.

## No-Public-Email Fallback

If no faculty roster can be extracted and no verified personal faculty email is available, the app first returns one publicly
published generic contact for the verified department, such as:

```text
Department Contact,nursing@university.edu
```

If no suitable department address is published, it returns one best-fit official
institutional contact for a medical conference invitation. Faculty affairs, academic
affairs, medical education, continuing medical education, events, outreach, and
communications addresses are preferred over a general information address. Admissions,
webmaster, support, billing, privacy, careers, and HR addresses are rejected as poor fits.

Every fallback address must be visibly published on an official or affiliated
institutional page. The app never invents or predicts a fallback email.

## Run Locally

```bash
python -m venv .venv
.venv\Scripts\activate
pip install -r requirements.txt
streamlit run app.py
```

On macOS or Linux, activate the environment with:

```bash
source .venv/bin/activate
```

## Deploy On Streamlit Community Cloud

1. Create a GitHub repository.
2. Upload only these files to the repository root:
   - `app.py`
   - `requirements.txt`
   - `packages.txt`
   - `README.md`
   - `.gitignore`
   - `assets/aventis-logo.png`
   - `assets/medical-globe-background-4k.jpg`
3. Go to Streamlit Community Cloud.
4. Select the repository.
5. Set the main file path to `app.py`.
6. Deploy.

## Example Search

Try:

- Country: `United States`
- State / Province / Region: `Alabama`
- Department / Specialty: `Obstetrics and Gynecology`

Then click **Discover Institutions** and select one or more institutions. Use the default
manual mode for supplied faculty pages, or switch to **Automatic website search**.

The recommended workflow is:

1. Click **Discover Institutions**.
2. Open an institution's displayed official website.
3. Navigate to the requested department's faculty, people, or provider page.
4. Paste that URL under the institution. Multiple URLs can be supplied, one per line.
5. Click **Extract Contacts from Faculty Pages**.

Manual faculty-page mode verifies every supplied URL against the institution's official
or officially linked affiliated domains. It reuses the same profile, institutional-email,
reconciliation, diagnostics, fallback-contact, and CSV rules as automatic mode, but skips
broad page discovery and the independent web-search audit. On an explicitly supplied
directory, every valid named roster member is retained. Emails and phones are optional
enrichment fields, never admission requirements for the final roster.

For stateful public directories such as PeopleSoft, the app submits the visible public
department-search form and follows the matching department result in the same session.
When a directory keeps its result only in the user's browser cookies, copy the visible
result page and paste it into **Visible directory results**; the manual extractor pairs
each institutional email with the nearest person name and includes every visible contact.

Institution discovery verifies the root website brand, academic or teaching-health
identity, selected location, and selected-specialty evidence before showing a result.
Regional medical-school pathways and official clerkship or clinical-site pages count as
evidence for both the local teaching institution and its partner medical school. Page
headlines, job listings, directory sites, default server pages, and out-of-location
institutions are rejected.

The institution search uses a live activity feed tied to actual crawler stages. Completed
institutions remain visible, the current and next institutions are identified, and the
percentage bar is kept as a secondary indicator.

The interface uses the supplied medical-technology artwork as a softly desaturated,
responsive watermark on a neutral charcoal background. The image is also embedded as a
fallback so it remains available if an asset is omitted during deployment. Motion is
disabled automatically for users who prefer reduced motion. Request throttling remains
enabled internally without occupying a permanent settings sidebar.

The crawler does not cap the number of institutions, department pages, faculty pages,
profiles, pagination links, sitemap entries, or PDF pages it processes. Broad searches
can therefore take longer. A small internal request delay keeps crawling polite without
placing artificial crawl limits in the interface.

## Known Limitations

- Some websites block automated requests.
- JavaScript-only directories use a Playwright/Chromium fallback when dynamic-page
  signals are detected; sites that block browsers can still require manual review.
- Some institutions do not publish public personal faculty emails.
- Sites with unusual HTML may require manual review.
- Search results depend on the availability and quality of public web search.
- Official PDFs are supported with lightweight text extraction, but complex scanned PDFs may not yield usable text.
- Very large multi-domain academic medical centers can take longer than 20 minutes when
  the unrestricted second-pass audit is enabled. The live activity feed remains active,
  but production deployments may eventually benefit from a persistent background-job
  queue so these crawls can resume independently of one Streamlit session.
