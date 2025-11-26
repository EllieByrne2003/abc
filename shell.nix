{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
    buildInputs = with pkgs; [
        git
        gcc
        gdb
        gnumake

        readline
    ];
}