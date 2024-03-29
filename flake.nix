{
  description = "A parametric Fitch-style modal lambda calculus";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-23.05";

  outputs = { self, nixpkgs }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;

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
      latex = pkgs.texlive.combine {
        inherit (pkgs.texlive) scheme-basic latexmk luatex
          biber biblatex biblatex-ieee
          pgf mathtools stmaryrd mathpartir listings
          parskip titlesec microtype;
        inherit fitch;
      };

      agdaPackage = pkgs.agdaPackages.mkDerivation {
        pname = "pfm-lambda";
        version = "1.0.0";
        src = self;
        buildInputs = [ pkgs.agdaPackages.standard-library ];
        meta = {};
      };

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
    in {
      packages.x86_64-linux = { default = agdaPackage; inherit paper; };

      devShells.x86_64-linux = {
        default = pkgs.mkShell { inputsFrom = [ agdaPackage paper ]; };
        agda = pkgs.mkShell { inputsFrom = [ agdaPackage ]; };
      };
    };
}
