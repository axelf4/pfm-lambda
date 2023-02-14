{
  outputs = { self, nixpkgs }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      agda = pkgs.agda.withPackages (ps: with ps; [
        standard-library
      ]);
    in {
      devShells.x86_64-linux.default = pkgs.mkShell {
        buildInputs = [ agda ];
      };
    };
}
