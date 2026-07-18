{
  description = "A parametric Fitch-style modal lambda calculus";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;

      latex-fitch = pkgs.stdenvNoCC.mkDerivation {
        pname = "fitch";
        version = "1.6";
        src = pkgs.fetchurl {
          url = "http://www.actual.world/resources/tex/sty/kluwer/edited/fitch.sty";
          sha256 = "lFFiY3Xq2GOUJQ65VLXcd0XHDBMULvyqJmqMg0sMK4I=";
        };
        preferLocalBuild = true;
        outputs = [ "tex" ];
        dontUnpack = true;
        preHook = ''out="''${tex-}"'';
        installPhase = ''
          runHook preInstall
          install -D $src $tex/tex/latex/misc/$pname.sty
          runHook postInstall
        '';
        passthru.tlType = "run";
      };
      texlive-fitch.pkgs = [ latex-fitch ];
      latex = pkgs.texliveBasic.withPackages (ps: with ps; [
        latexmk luatex
        biber biblatex biblatex-ieee
        pgf mathtools stmaryrd mathpartir listings
        parskip titlesec microtype
        texlive-fitch
      ]);

      src = builtins.path { path = ./.; name = "pfm-lambda"; };
      agdaPackage = pkgs.agdaPackages.mkDerivation {
        pname = "pfm-lambda";
        version = "1.0.0";
        inherit src;
        buildInputs = [ pkgs.agdaPackages.standard-library ];
        meta = {};
      };
      paper = pkgs.stdenvNoCC.mkDerivation {
        name = "paper";
        inherit src;
        sourceRoot = "pfm-lambda/paper";
        nativeBuildInputs = [ latex pkgs.writableTmpDirAsHomeHook ];
        buildPhase = ''latexmk -lualatex -interaction=nonstopmode thesis.tex'';
        installPhase = ''cp thesis.pdf $out'';
      };
    in {
      packages.x86_64-linux = { default = agdaPackage; inherit paper; };

      devShells.x86_64-linux = {
        default = pkgs.mkShell { inputsFrom = [ agdaPackage paper ]; };
        agda = pkgs.mkShell { inputsFrom = [ agdaPackage ]; };
      };
    };
}
