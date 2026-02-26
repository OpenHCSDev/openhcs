.PHONY: dev install-hooks help

help: ## Show this help
	@grep -E '^[a-zA-Z_-]+:.*?## ' $(MAKEFILE_LIST) | sort | awk 'BEGIN {FS = ":.*?## "}; {printf "\033[36m%-20s\033[0m %s\n", $$1, $$2}'

dev: install-hooks ## Set up development environment (installs hooks and dependencies)
	pip install -e ".[dev]"
	@echo "✅ Development environment ready!"
	@echo "Hooks are installed and will auto-update submodules on git operations."

install-hooks: ## Install git hooks for submodule auto-update
	@git config core.hooksPath hooks
	@echo "✅ Git hooks installed"

update-submodules: ## Manually update all submodules to latest
	git submodule update --remote

status: ## Show submodule status
	git submodule status
