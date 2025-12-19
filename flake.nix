{
  description = "Dependents for running HTML of Notebook.";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }: let

    system = "x86_64-linux";

    pkgs = nixpkgs.legacyPackages.${system};

    pythonEnv = pkgs.python313.withPackages (ps: with ps; [
      livereload
    ]);

  in {

    devShells.${system}.default = pkgs.mkShell {

      nativeBuildInputs = [
        pkgs.lean4
        pkgs.gcc
        pkgs.nodejs_24
        pythonEnv
      ];

      shellHook = "echo 'Develop Env is Set.'";
    };
  };
}

