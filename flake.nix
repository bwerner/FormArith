{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-24.05";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      self,
      flake-utils,
      nixpkgs,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system; };
        coqPackages = pkgs.coqPackages_8_19;
      in
      rec {
        packages = {
          theories = let
            autosubst = coqPackages.mkCoqDerivation {
              pname = "autosubst";
              version = "1.9";

              # The tarball is not present in the release
              src = pkgs.fetchFromGitHub {
                owner = "coq-community";
                repo = "autosubst";
                rev = "v1.9";
                sha256 = "sha256-XiLZjMc+1iwRGOstfLm/WQRF6FTdX6oJr5urn3wmLlA=";
              };
            };
          in coqPackages.mkCoqDerivation rec {
            pname = "FormArith";
            opam-name = "FormArith";
            version = "0.1.0";

            src = ./.;
            useDune = true;

            propagatedBuildInputs = [ autosubst ];
          };

          default = packages.theories;
        };

        devShells.default = pkgs.mkShell {
          inputsFrom = with packages; [ theories ];
          packages = with coqPackages; [ vscoq-language-server ];
        };

        formatter = pkgs.nixfmt-rfc-style;
      }
    );
}
