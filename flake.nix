{
  description = "Dependents for running HTML of Notebook.";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }: let

    system = "x86_64-linux";

    pkgs = nixpkgs.legacyPackages.${system};

    python = pkgs.python313;

    pythonEnv = python.withPackages (ps: with ps; [
      livereload
    ]);

  in {

    devShells.${system}.default = pkgs.mkShell {

      nativeBuildInputs = [
        pythonEnv
      ];

      shellHook = "echo 'Python ENV is ready.'";
    };
  };
}

