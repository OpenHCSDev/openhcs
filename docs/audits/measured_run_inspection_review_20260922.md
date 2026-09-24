# Targeted review: measured ordinary-pipeline inspection

The changed authority is the benchmark-only evidence layer around the ordinary
OpenHCS pipeline submission. The wrapper now retains exact submitted pipeline
source, a rendered global configuration, a typed completed-run receipt, and a
validated runtime observation. The CLI `inspect-measured` command and two
expert local MCP capabilities project the same bounded receipt inspection and
report. They do not submit jobs, duplicate runtime status, or load the pickled
observation during inspection. The existing comparison-suite inspector remains
separate because its lifecycle and native-reference evidence are different.

I reviewed the affected claims and audience boundaries in the README, MCP
distribution explanation, measurement-equivalence explanation, extension
workflow reference, module-structure concept page, MCP client how-to, research
impact appendix, and biologist onboarding page. The first six needed focused
clarification; the final two remain accurate without added tool detail. This is
an authority-delta review, not a full editorial audit of those pages.

Evidence: 41 focused benchmark/control tests and two live ordinary-pipeline
integration tests passed. The inspector checks declared source SHA-256 values
and confined file presence under the selected run directory; tests cover
tampering and a receipt pointing outside that directory. A fresh local MCP
client discovered and invoked both expert tools; the installed-wheel CI smoke
now repeats that proof outside the checkout. No live benchmark submission over
MCP, comparative benchmark, or scientific parity claim is made.
