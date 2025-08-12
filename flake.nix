{
  description = "A very basic flake";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
  };

  outputs = { self, nixpkgs }: let
    for-all-systems = f:
      nixpkgs.lib.genAttrs [
        "x86_64-linux"
        "aarch64-darwin"
      ] (system: f nixpkgs.legacyPackages.${system});
  in {
    devShells = for-all-systems (pkgs: {
      default = pkgs.mkShell {
        shellHook = ''
          unset SOURCE_DATE_EPOCH
          unset COQPATH
        '';
        packages = with pkgs; [
          coq
          coqPackages.stdlib
          # (texlive.combine {
          #   inherit (texlive) scheme-basic collection-fontsrecommended
          #   dvisvgm dvipng # for preview and export as html
          #   biblatex latexmk babel-portuges
          #   abntex2 memoir xpatch booktabs textcase enumitem supertabular listings
          #   lastpage glossaries
          #   wrapfig amsmath ulem hyperref capt-of;
          # })
          typst
          gnumake
        ];
      };
    });
  };
}
