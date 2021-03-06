{ pkgs ? import <nixpkgs> {}
, haskellPackages ? pkgs.haskellPackages
, withHoogle ? false }:

let overrideCabal = pkg: pkgs.haskell.lib.overrideCabal pkg ({ buildDepends ? [], ... }: {
      buildDepends = buildDepends ++ [ pkgs.cabal-install haskellPackages.hsdev haskellPackages.hlint ];
    });

in (overrideCabal (import ./default.nix { inherit pkgs haskellPackages withHoogle; })).env
