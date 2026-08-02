{
  description = "VeriBiota CI, packages, and development environment";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs, ... }:
    let
      systems = [ "x86_64-linux" ];
      forAllSystems = nixpkgs.lib.genAttrs systems;
    in
    {
      packages = forAllSystems (system:
        let
          pkgs = import nixpkgs { inherit system; };
          python = pkgs.python3;
          src = pkgs.lib.cleanSourceWith {
            src = ./.;
            filter = path: type:
              let
                base = baseNameOf path;
              in
              !(builtins.elem base [
                ".git"
                ".jj"
                ".lake"
                "build"
                "dist"
                "node_modules"
                "result"
                "site"
                "target"
              ]);
          };
        in
        rec {
          veribiota-python = python.pkgs.buildPythonApplication {
            pname = "veribiota";
            version = "0.1.0";
            inherit src;
            pyproject = true;
            build-system = [ python.pkgs.setuptools ];
            pythonImportsCheck = [ "veribiota" "veribiota.adapter" ];
          };

          biosim-checks = pkgs.rustPlatform.buildRustPackage {
            pname = "biosim-checks";
            version = "0.1.0";
            inherit src;
            sourceRoot = "source/engine/biosim-checks";
            cargoLock.lockFile = ./engine/biosim-checks/Cargo.lock;
          };

          veribiota-rust-adapter = pkgs.rustPlatform.buildRustPackage {
            pname = "veribiota-rust-adapter";
            version = "0.1.0";
            inherit src;
            sourceRoot = "source/adapters/rust";
            cargoLock.lockFile = ./adapters/rust/Cargo.lock;
          };

          docs = pkgs.stdenvNoCC.mkDerivation {
            pname = "veribiota-docs";
            version = "0.1.0";
            inherit src;
            nativeBuildInputs = [
              python.pkgs.mkdocs
              python.pkgs.mkdocs-material
            ];
            buildPhase = ''
              runHook preBuild
              mkdocs build --strict
              runHook postBuild
            '';
            installPhase = ''
              runHook preInstall
              mkdir -p "$out"
              cp -R site/. "$out/"
              runHook postInstall
            '';
          };

          default = veribiota-python;
        });

      checks = forAllSystems (system:
        let
          pkgs = import nixpkgs { inherit system; };
          python = pkgs.python3;
          packages = self.packages.${system};
          src = pkgs.lib.cleanSourceWith {
            src = ./.;
            filter = path: type:
              let
                base = baseNameOf path;
              in
              !(builtins.elem base [
                ".git"
                ".jj"
                ".lake"
                "build"
                "dist"
                "node_modules"
                "result"
                "site"
                "target"
              ]);
          };

          nodeModules = pkgs.importNpmLock.buildNodeModules {
            npmRoot = src;
            nodejs = pkgs.nodejs_24;
          };

          runRepoCheck = name: nativeBuildInputs: script:
            pkgs.runCommandLocal "veribiota-${name}-check"
              {
                inherit src;
                nativeBuildInputs = nativeBuildInputs ++ [
                  pkgs.coreutils
                  pkgs.git
                  pkgs.gnumake
                  pkgs.jq
                ];
              }
              ''
                set -euo pipefail
                cp -R "$src" repo
                chmod -R u+w repo
                cd repo
                ${script}
                touch "$out"
              '';
        in
        {
          inherit (packages) biosim-checks docs veribiota-python veribiota-rust-adapter;

          node-schema = pkgs.runCommandLocal "veribiota-node-schema-check"
            {
              inherit src;
              nativeBuildInputs = [
                pkgs.coreutils
                pkgs.nodejs_24
                nodeModules
              ];
            }
            ''
              set -euo pipefail
              cp -R "$src" repo
              chmod -R u+w repo
              cd repo
              ln -s ${nodeModules}/node_modules node_modules
              npm run check
              touch "$out"
            '';

          python-tests = runRepoCheck "python-tests"
            [ (python.withPackages (ps: [ ps.pytest ps.jsonschema ])) ]
            ''
              python -m unittest discover -s tests/python -p 'test_*.py'
              python -m pytest tests/python
            '';

          rust-validation = runRepoCheck "rust-validation"
            [
              pkgs.rustfmt
              packages.veribiota-rust-adapter
            ]
            ''
              find engine/biosim-checks adapters/rust -name '*.rs' -print0 | xargs -0 rustfmt --check
              veribiota-rust-adapter \
                --checks examples/checks.mass.json \
                --trajectory examples/trajectory.sample.jsonl
              veribiota-rust-adapter \
                --checks examples/checks.mass.json \
                --trajectory examples/trajectory.counts.jsonl
              set +e
              veribiota-rust-adapter \
                --checks examples/checks.mass.json \
                --trajectory examples/trajectory.counts.violation.jsonl
              status=$?
              set -e
              test "$status" -eq 2
            '';

          dockerfile = runRepoCheck "dockerfile"
            [ pkgs.hadolint ]
            ''
              hadolint --ignore DL3008 --ignore DL4006 Dockerfile
            '';

          repo-validation = runRepoCheck "repo-validation"
            [
              (python.withPackages (ps: [ ps.pytest ]))
              pkgs.nodejs_24
              nodeModules
            ]
            ''
              ln -s ${nodeModules}/node_modules node_modules
              npm run check
              python -m pytest tests/python
              node --input-type=module <<'NODE'
              import { readFileSync } from "node:fs";
              import { globSync } from "glob";
              import YAML from "yaml";

              for (const path of globSync(".github/workflows/*.yml")) {
                YAML.parse(readFileSync(path, "utf8"));
              }
              console.log("workflow yaml parse ok");
              NODE
            '';
        });

      apps = forAllSystems (system:
        let
          pkgs = import nixpkgs { inherit system; };
          lean-check = pkgs.writeShellApplication {
            name = "veribiota-lean-check";
            runtimeInputs = [
              pkgs.coreutils
              pkgs.curl
              pkgs.elan
              pkgs.git
            ];
            text = ''
              set -euo pipefail
              toolchain="$(cat lean-toolchain)"
              elan toolchain install "$toolchain"
              elan default "$toolchain"
              lake update
              lake exe cache get
              lake build
              lake exe biosim_tests
            '';
          };
          tier0-snapshots = pkgs.writeShellApplication {
            name = "veribiota-tier0-snapshots";
            runtimeInputs = [
              pkgs.coreutils
              pkgs.curl
              pkgs.elan
              pkgs.git
              pkgs.jq
              (pkgs.python3.withPackages (ps: [ ps.jsonschema ]))
            ];
            text = ''
              set -euo pipefail
              toolchain="$(cat lean-toolchain)"
              elan toolchain install "$toolchain"
              elan default "$toolchain"
              lake update
              lake exe cache get
              lake build
              lake exe biosim_tests

              rm -rf ci_signatures
              mkdir -p ci_signatures
              jq .input Tests/profiles/global_affine_v1/match_pass.json \
                | ./veribiota check alignment global_affine_v1 - --snapshot-out ci_signatures/global_affine_v1.sig.json --compact
              jq .input Tests/profiles/edit_script_normal_form_v1/pass_simple_normal.json \
                | ./veribiota check edit edit_script_normal_form_v1 - --snapshot-out ci_signatures/edit_script_normal_form_v1.sig.json --compact
              jq .input Tests/profiles/prime_edit_plan_v1/pass_simple.json \
                | ./veribiota check prime prime_edit_plan_v1 - --snapshot-out ci_signatures/prime_edit_plan_v1.sig.json --compact
              jq .input Tests/profiles/pair_hmm_bridge_v1/pass_simple.json \
                | ./veribiota check hmm pair_hmm_bridge_v1 - --snapshot-out ci_signatures/pair_hmm_bridge_v1.sig.json --compact
              jq .input Tests/profiles/vcf_normalization_v1/ok_minimal.json \
                | ./veribiota check vcf vcf_normalization_v1 - --snapshot-out ci_signatures/vcf_normalization_minimal.sig.json --compact
              jq .input Tests/profiles/vcf_normalization_v1/ok_complex.json \
                | ./veribiota check vcf vcf_normalization_v1 - --snapshot-out ci_signatures/vcf_normalization_complex.sig.json --compact

              python .github/scripts/validate_snapshots.py ci_signatures
            '';
          };
          codeql-cpp-build = pkgs.writeShellApplication {
            name = "veribiota-codeql-cpp-build";
            runtimeInputs = [
              pkgs.cargo
              pkgs.ccache
              pkgs.cmake
              pkgs.coreutils
              pkgs.gcc
              pkgs.gnumake
              pkgs.rustc
            ];
            text = ''
              set -euo pipefail

              cargo build --manifest-path engine/biosim-checks/Cargo.toml

              checks_lib=""
              for candidate in \
                "$PWD/engine/biosim-checks/target/debug/deps/libbiosim_checks.so" \
                "$PWD/engine/biosim-checks/target/debug/deps/libbiosim_checks.dylib" \
                "$PWD/engine/biosim-checks/target/debug/deps/libbiosim_checks.a" \
                "$PWD/engine/biosim-checks/target/debug/deps/biosim_checks.lib"; do
                if [[ -f "$candidate" ]]; then
                  checks_lib="$candidate"
                  break
                fi
              done

              if [[ -z "$checks_lib" ]]; then
                echo "libbiosim_checks not found after cargo build. Contents:" >&2
                ls -la engine/biosim-checks/target/debug/deps >&2 || true
                exit 1
              fi

              cmake -S adapters/cpp -B adapters/cpp/build \
                -DCMAKE_BUILD_TYPE=Debug \
                -DCMAKE_C_COMPILER_LAUNCHER=ccache \
                -DCMAKE_CXX_COMPILER_LAUNCHER=ccache \
                -DVERIBIOTA_CHECKS_LIB="$checks_lib"
              cmake --build adapters/cpp/build --config Debug -j"$(nproc)"
            '';
          };
        in
        {
          lean-check = {
            type = "app";
            program = "${lean-check}/bin/veribiota-lean-check";
            meta.description = "Run the VeriBiota Lean build and biosim profile tests";
          };
          tier0-snapshots = {
            type = "app";
            program = "${tier0-snapshots}/bin/veribiota-tier0-snapshots";
            meta.description = "Run VeriBiota Tier 0 snapshot attestation checks";
          };
          codeql-cpp-build = {
            type = "app";
            program = "${codeql-cpp-build}/bin/veribiota-codeql-cpp-build";
            meta.description = "Build VeriBiota's C++ adapter for CodeQL manual C/C++ analysis";
          };
        });

      devShells = forAllSystems (system:
        let
          pkgs = import nixpkgs { inherit system; };
        in
        {
          default = pkgs.mkShell {
            packages = [
              pkgs.cargo
              pkgs.ccache
              pkgs.cmake
              pkgs.elan
              pkgs.gnumake
              pkgs.hadolint
              pkgs.jq
              pkgs.nodejs_24
              pkgs.openssl
              pkgs.rustc
              pkgs.rustfmt
              pkgs.python3
              pkgs.python3Packages.jsonschema
              pkgs.python3Packages.mkdocs
              pkgs.python3Packages.mkdocs-material
              pkgs.python3Packages.pytest
            ];
          };
        });
    };
}
