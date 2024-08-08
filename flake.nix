{
  inputs = {
    opam-nix.url = "github:tweag/opam-nix";
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.follows = "opam-nix/nixpkgs";
    opam-repository = {
      url = "github:ocaml/opam-repository";
      flake = false;
    };
    opam-coq-archive = {
      url = "github:coq/opam-coq-archive";
      flake = false;
    };
  };
  outputs = { self, flake-utils, opam-nix, opam-repository, opam-coq-archive, nixpkgs }@inputs:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        on = opam-nix.lib.${system};
        repos = [ opam-repository ];
        localPackagesQuery = builtins.mapAttrs (_: pkgs.lib.last)
          (on.listRepo (on.makeOpamRepo ./.));
        devPackagesQuery = {
          # Developer environment
          coq                   = "8.19.2";
          vscoq-language-server = "2.1.7";
        };
        query = devPackagesQuery // {
          ## You can force versions of certain packages here, e.g:
          ## - force the ocaml compiler to be taken from opam-repository:
          ocaml-base-compiler = "*";
          ## - or force the compiler to be taken from nixpkgs and be a certain version:
          # ocaml-system = "4.14.0";
          ## - or force ocamlfind to be a certain version:
          # ocamlfind = "1.9.2";
        };
        scope = on.buildOpamProject' { inherit repos; } ./. query;
        overlay = final: prev:
          {
            # You can add overrides here
          };
        scope' = scope.overrideScope' overlay;
        # Packages from devPackagesQuery
        devPackages = builtins.attrValues
          (pkgs.lib.getAttrs (builtins.attrNames devPackagesQuery) scope');
        # Packages in this workspace
        packages =
          pkgs.lib.getAttrs (builtins.attrNames localPackagesQuery) scope';
      in {
        legacyPackages = scope';

        packages = packages // { default = packages.coq-uplc; };

        devShells.default = pkgs.mkShell {
          inputsFrom = builtins.attrValues packages;
          buildInputs = devPackages ++ [
            # You can add packages from nixpkgs here
          ];
        };
      });
}
