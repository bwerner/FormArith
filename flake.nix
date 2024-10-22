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
          theories = coqPackages.mkCoqDerivation rec {
            pname = "FormArith";
            opam-name = "FormArith";
            version = "0.1.0";

            src = ./.;
            useDune = true;
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
