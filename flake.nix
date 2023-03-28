{
  outputs = { self, nixpkgs }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      agda = pkgs.agda.withPackages (ps: with ps; [
        standard-library
      ]);
      latex = with pkgs; texlive.combine {
        inherit (texlive) scheme-basic latexmk luatex fontspec
          biber biblatex
          catchfile pgf transparent xcolor trimspaces koma-script svg
          scalerel mathtools stmaryrd mathpartir
          listings booktabs
          microtype crimson;
      };
    in {
      devShells.x86_64-linux.default = pkgs.mkShell {
        buildInputs = [ agda latex ];
      };

      packages.x86_64-linux = {
        paper = pkgs.stdenvNoCC.mkDerivation {
          name = "paper";
          src = self;
          sourceRoot = "source/paper";
          nativeBuildInputs = [ latex ];
          buildPhase = ''
            mkdir -p .cache/texmf-var
            TEXMFVAR=.cache/texmf-var \
              latexmk -interaction=nonstopmode -lualatex thesis.tex
          '';
          installPhase = ''
            cp thesis.pdf $out
          '';
        };
      };
    };
}
