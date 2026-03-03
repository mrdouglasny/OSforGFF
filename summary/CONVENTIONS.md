# Summary File Conventions

This file documents LaTeX and formatting rules for the auto-generated summaries
in `summary/OSforGFF/`. Re-run `/lean-summarize <file>` to refresh any summary.

## Known GitHub rendering constraints

GitHub uses **KaTeX** to render math in markdown. KaTeX is more restricted than
full LaTeX or MathJax. The following rules prevent rendering failures:

### Banned macros

| Do NOT use | Use instead | Example |
|---|---|---|
| `\operatorname{Re}` | `\mathrm{Re}` | $\mathrm{Re}(z)$ |
| `\operatorname{tr}` | `\mathrm{tr}` | $\mathrm{tr}(A)$ |
| `\operatorname{Im}` | `\mathrm{Im}` | $\mathrm{Im}(z)$ |
| `\operatorname{ofReal}` | `\mathrm{ofReal}` | $\mathrm{ofReal}(r)$ |
| `\operatorname{<any>}` | `\mathrm{<any>}` | — |
| `\DeclareMathOperator` | n/a (not supported) | — |

**Reason**: `\operatorname` is not in KaTeX's supported macro list. `\mathrm` is
equivalent for rendering purposes and works everywhere.

## Positive conventions

- **Norms**: `\lVert x \rVert` (not `\|x\|` or `||x||`)
- **Absolute values**: `\lvert x_0 \rvert` (not `|x_0|`)
- **Real part**: `\mathrm{Re}` (not `\text{Re}` or `\operatorname{Re}`)
- **Trace**: `\mathrm{tr}` (not `\text{tr}` or `\operatorname{tr}`)
- **Named predicates/constructors**: `\mathrm{OS4\_Clustering}`, `\mathrm{ofReal}`, etc.
- **Display math**: use `$$...$$` for equations that are the main point of a theorem
- **Inline math**: use `$...$` for short expressions within prose

## How to fix existing summaries

If a summary was generated with banned macros, run:
```bash
find summary -name "*.md" -exec sed -i '' 's/\\operatorname{\([^}]*\)}/\\mathrm{\1}/g' {} \;
```
Then commit the result.
