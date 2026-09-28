# Keep the skill aligned with an OpenHCS installation

The OpenHCS wheel and source distribution carry the complete canonical skill,
including this entrypoint, references and UI metadata. MCP knowledge uses the
same source references. Installing the Python package does not silently change
agent configuration or write a skill into a user's home directory.

## Add a managed skill to a harness

Choose the harness's actual skill-discovery directory, then use the Python
environment that runs the intended OpenHCS MCP server:

```sh
python -m openhcs.cli skills sync --skills-dir /absolute/path/to/harness/skills --dry-run
python -m openhcs.cli skills sync --skills-dir /absolute/path/to/harness/skills
```

The command is headless and does not start MCP, a viewer or a model. It creates
the plugin-declared skill directories and prints JSON status with the package
version. It requires an explicit destination; it does not guess client paths or
install the MCP connection itself. For a packaged plugin, use the harness's
plugin installation/update flow instead of installing a duplicate direct skill.

Codex documents user-level discovery under `$HOME/.agents/skills` and repository
discovery under `.agents/skills`. Your existing configuration may use a different
supported location. Check what is already active before choosing the destination;
two skills with the same name are not automatically merged. Other harnesses
need their own documented discovery path. See the [official skill documentation](https://learn.chatgpt.com/docs/build-skills)
and [plugin packaging documentation](https://developers.openai.com/plugins/build/plugins).

## Refresh after a package upgrade

Run the same sync command with the newly installed OpenHCS environment after
each install or update. An opted-in setup/update script can make this its final
step; this PR does not automatically enrol native installers or in-app updates.
It exports the guidance from that installed package, not an unrelated checkout.
Do not assume a currently running agent has reread every instruction: use the
harness's refresh/restart behaviour when its active skill remains stale.

An unchanged managed copy is not rewritten. A changed release can replace a
copy only when its files still match the previous ownership receipt. The old
tree is retained at the reported `backup_path`, outside normal skill discovery,
so the previous version is recoverable.

## Resolve conflicts without losing local work

The command refuses unmarked directories, locally changed/added/deleted files,
symlinked skills and redirected destination ancestors. It does not provide a
force-overwrite flag. Preserve or reconcile custom work yourself, or choose a
separate destination that the harness explicitly loads. Do not install both
copies without considering duplicate discovery.

For a development symlink, update its canonical checkout while preserving dirty
work; the sync command deliberately will not replace it. Plain `pip install`
and `openhcs skills sync` have distinct responsibilities: package installation
and explicit harness registration. There is no universal cross-harness pip
post-install hook or guaranteed hot reload implied by this procedure.
