# Global Medical Faculty Contact Finder

A ready-to-deploy Streamlit app for finding publicly visible official faculty work emails from universities, colleges, medical schools, teaching hospitals, health-science institutions, and academic centres.

The app searches for answer-bearing official pages first, verifies the institution and
selected location from that evidence, and then follows only relevant official program,
department, directory, and profile pages. It does not use paid APIs, AI APIs, login-only
data, third-party people databases, or guessed email patterns.

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
schools. When a strong official academic candidate lacks specialty evidence in the first
result set, the app performs a targeted follow-up restricted to that institution's own
domain.

Country selection uses the full ISO country list. The location dropdown combines official country subdivisions with searchable city data, and includes an all-regions option.

## Output

The final table and downloadable CSV contain exactly two columns:

```text
Name,Email
```

If one verified faculty member has two different publicly visible official institutional emails, the app keeps two rows. Generic department fallback emails are never assigned to faculty members.

## Accuracy Rule

Accuracy is prioritized over quantity. A contact is returned only when:

- the person is associated with the selected department or a directly related academic unit,
- the person appears to be current faculty, academic teaching staff, or an eligible academic researcher,
- the email is visibly published on an official institutional teaching source,
- the email is an institutional work email, or a professional affiliate email explicitly
  published beside the faculty member on that verified teaching source,
- the name and email are locally associated on a profile, card, directory row, official PDF, or similar source.

The app never guesses, generates, constructs, infers, or predicts emails from names.

## No-Public-Email Fallback

If no verified personal faculty email is available, the app first returns one publicly
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
   - `README.md`
   - `.gitignore`
   - `assets/medical-technology-background.png`
3. Go to Streamlit Community Cloud.
4. Select the repository.
5. Set the main file path to `app.py`.
6. Deploy.

## Example Search

Try:

- Country: `United States`
- State / Province / Region: `Alabama`
- Department / Specialty: `Obstetrics and Gynecology`

Then click **Discover Institutions**, select one or more institutions, and click **Search Selected Institutions**.

Institution discovery verifies the root website brand, academic or teaching-health
identity, selected location, and selected-specialty evidence before showing a result.
Regional medical-school pathways and official clerkship or clinical-site pages count as
evidence for both the local teaching institution and its partner medical school. Page
headlines, job listings, directory sites, default server pages, and out-of-location
institutions are rejected.

The institution search uses a live activity feed tied to actual crawler stages. Completed
institutions remain visible, the current and next institutions are identified, and the
percentage bar is kept as a secondary indicator.

The interface uses the supplied medical-technology artwork as a responsive full-page
background with subtle movement. Motion is disabled automatically for users who prefer
reduced motion. Request throttling remains enabled internally without occupying a
permanent settings sidebar.

The crawler does not cap the number of institutions, department pages, faculty pages,
profiles, pagination links, sitemap entries, or PDF pages it processes. Broad searches
can therefore take longer. A small internal request delay keeps crawling polite without
placing artificial crawl limits in the interface.

## Known Limitations

- Some websites block automated requests.
- JavaScript-only directories may not expose faculty data in normal HTML.
- Some institutions do not publish public personal faculty emails.
- Sites with unusual HTML may require manual review.
- Search results depend on the availability and quality of public web search.
- Official PDFs are supported with lightweight text extraction, but complex scanned PDFs may not yield usable text.
