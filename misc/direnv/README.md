This folder contains `.envrc` files that are suitable to start from if you would like to use [direnv](https://direnv.net/) to manage your environment. To use one of them, issue the following command from the root of the repository:

```bash
# Copy one of the .envrc files to the root
cp misc/direnv/<envrc-file> .envrc

# Allow the .envrc to execute
direnv allow
```

Note that `.envrc` in the root of the repository is in `.gitignore`, meaning that you can change this file freely without affecting the git history. These files are available:

- `nix.envrc` use a Nix flake to install enter a devshell with all Miking dependencies.
