{
  outputs = { self, nixpkgs }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      agda = pkgs.agda.withPackages (ps: with ps; [
        standard-library
      ]);

      fitch.pkgs = [ (pkgs.runCommandLocal "fitch"
        {
          pname = "fitch";
          tlType = "run";
          src = pkgs.fetchurl {
            url = "http://www.actual.world/resources/tex/sty/kluwer/edited/fitch.sty";
            sha256 = "lFFiY3Xq2GOUJQ65VLXcd0XHDBMULvyqJmqMg0sMK4I=";
          };
        }
        ''mkdir -p $out/tex/latex && cp $src $out/tex/latex/"$pname".sty'') ];
      latex = with pkgs; texlive.combine {
        inherit (texlive) scheme-basic latexmk luatex
          biber biblatex
          pgf mathtools stmaryrd mathpartir;
        inherit fitch;
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
