
.PHONY: help
help:
	@echo "Usage: make <target>"
	@echo
	@echo "Targets:"
	@echo "  help  -- show this help"
	@echo "  shell -- nix develop"
	@echo "  build -- dune build"
	@echo "  clean -- dune clean"

.PHONY: shell
shell:
	nix develop

.PHONY: build
build:
	dune build

.PHONY: clean
clean:
	dune clean
