# Global Medical Faculty Contact Finder

A ready-to-deploy Streamlit app for finding publicly visible official faculty work emails from universities, colleges, medical schools, teaching hospitals, health-science institutions, and academic centres.

The app uses web search plus direct official-site crawling. It does not use paid APIs, AI APIs, login-only data, third-party people databases, or guessed email patterns.

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
- the email is visibly published on an official institutional source,
- the email is an official institutional work email,
- the name and email are locally associated on a profile, card, directory row, official PDF, or similar source.

The app never guesses, generates, constructs, infers, or predicts emails from names.

## No-Public-Email Fallback

If an institution publishes faculty names but no verified personal faculty emails, the app can return exactly one generic department contact such as:

```text
Department Contact,nursing@university.edu
```

This happens only when the department is verified and the generic address appears on an official department or university page.

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
3. Go to Streamlit Community Cloud.
4. Select the repository.
5. Set the main file path to `app.py`.
6. Deploy.

## Example Search

Try:

- Country: `United States`
- State / Province / Region: `Alabama`
- Department / Specialty: `Nursing`

Then click **Discover Institutions**, select one or more institutions, and click **Search Selected Institutions**.

## Known Limitations

- Some websites block automated requests.
- JavaScript-only directories may not expose faculty data in normal HTML.
- Some institutions do not publish public personal faculty emails.
- Sites with unusual HTML may require manual review.
- Search results depend on the availability and quality of public web search.
- Official PDFs are supported with lightweight text extraction, but complex scanned PDFs may not yield usable text.
