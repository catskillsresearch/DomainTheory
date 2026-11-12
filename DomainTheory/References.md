# References

The bibliography is maintained in [`references.bib`](../references.bib) and
processed by BibTeX (`unsrt`) when building `DomainTheory.pdf`. Notes use pandoc
citation syntax (`[@key]`); the TeX build rewrites those to `\cite` before
pandoc. Regenerate the `.bib` from a prose dump with
`python3 scripts/md_refs_to_bib.py` if needed.
