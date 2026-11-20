# Building the paper

Use pdfLaTeX and BibTeX from TeX Live 2026 with AMS-LaTeX, AMSFonts,
Latin Modern and hyperref. The Latin Modern Type 1 outlines must be
available to pdfTeX. Use Poppler for the PDF checks.

In a clean copy of `source/`, run the following commands.

```sh
export TZ=UTC LC_ALL=C SOURCE_DATE_EPOCH=1795176000 FORCE_SOURCE_DATE=1
pdflatex -recorder -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -recorder -interaction=nonstopmode -halt-on-error main.tex
pdflatex -recorder -interaction=nonstopmode -halt-on-error main.tex
pdffonts main.pdf
pdfinfo main.pdf
```

The final TeX and BibTeX logs should be free of warnings. The PDF
should contain only embedded Type 1 fonts and include the title,
author, MSC subject and keywords in its metadata. The source includes
`main.bbl` so the bibliography is also available to pdfLaTeX directly.

Run `sha256sum -c SHA256SUMS` from the package root to verify the
distributed files.
