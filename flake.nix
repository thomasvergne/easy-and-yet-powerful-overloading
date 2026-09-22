{
  description = "Easy and Yet Powerful Overloading";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }:
    let
      supportedSystems = [ "aarch64-darwin" "x86_64-darwin" ];
      forEachSupportedSystem = f:
        nixpkgs.lib.genAttrs supportedSystems
          (system: f {
            pkgs = import nixpkgs { inherit system; };
          });
    in {
      devShells = forEachSupportedSystem ({ pkgs }: {
        default = pkgs.mkShell {
          packages = [
            (pkgs.texlive.combine {
              inherit (pkgs.texlive)
                scheme-small
                latexmk
                luatex
                biber
                amsmath
                graphics
                koma-script
                babel-german
                hyperref
                fontawesome5
                tcolorbox;
            })
            pkgs.skim
            pkgs.git
          ];
        };
      });
    };
}