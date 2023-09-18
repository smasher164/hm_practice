{
  description = "hm_practice";
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    let supportedSystems = [ "aarch64-linux" "i686-linux" "x86_64-linux" ];
    in flake-utils.lib.eachSystem supportedSystems (system:
      let
        ocaml5Overlay = final: prev: {
          ocamlPackages = prev.ocaml-ng.ocamlPackages_5_0;
        };
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ (ocaml5Overlay) ];
        };
      in {
        devShell = pkgs.mkShell {
          buildInputs = with pkgs.ocamlPackages; [
            ocaml
            ocaml-lsp
            dune_3
            odoc
            utop
            findlib
            ppx_inline_test
            ocamlformat
            containers
            batteries
          ];
        };
      });
}
