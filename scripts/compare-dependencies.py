import contextlib
import io
import json
import subprocess
import sys

def tree(url, rev):
    if not url.startswith("https://github.com/"):
        return rev
    return f"[{rev}]({url}/tree/{rev})"


def compare(url1, url2, rev1, rev2):
    if not url1.startswith("https://github.com/") or  not url2.startswith("https://github.com/"):
        return f"{rev1} to {rev2}"
    if url1 != url2:
        return f"{tree(url1, rev1)} to {tree(url2, rev2)}"
    return f"[{rev1} to {rev2}]({url1}/compare/{rev1}..{rev2})"


def package_map(o):
    packages = json.loads(o)["packages"]
    map = {}
    for p in packages:
        if p["name"] in map:
            raise ValueError(f"Duplicated package {p['name']}")
        map[p["name"]] = p
    return map


def compare_manifests(before, after):
    b = package_map(before)
    a = package_map(after)
    names = sorted(b.keys() | a.keys())
    for n in names:
        if n not in a:
            print(f"Package {n} removed at commit {tree(b[n]['url'], b[n]['rev'])}")
        elif n not in b:
            print(f"Package {n} added at commit {tree(a[n]['url'], a[n]['rev'])}")
        elif a[n]['rev'] == b[n]['rev'] and a[n]['url'] == b[n]['url']:
            print(f"Package {n} unchanged")
        else:
            c = compare(b[n]['url'], a[n]['url'], b[n]['rev'], a[n]['rev'])
            print(f"Package {n} moved from commit {c}")

def main(rev1, rev2):
    before = subprocess.check_output(["git", "show", rev1 + ":lake-manifest.json"])
    after = subprocess.check_output(["git", "show", rev2 + ":lake-manifest.json"])
    compare_manifests(before, after)

def test():
    before = b"""
{"version": "1.1.0",
 "packagesDir": ".lake/packages",
 "packages":
 [{"url": "https://github.com/leanprover-community/batteries",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "46fed98b5cac2b1ea64e363b420c382ed1af0d85",
   "name": "batteries",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": false,
   "configFile": "lakefile.lean"},
  {"url": "https://github.com/leanprover-community/aesop",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "bea1488cd9a74883511471a6d3fa954a3ac40809",
   "name": "aesop",
   "manifestFile": "lake-manifest.json",
   "inputRev": "master",
   "inherited": false,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/ProofWidgets4",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "eb08eee94098fe530ccd6d8751a86fe405473d4c",
   "name": "proofwidgets",
   "manifestFile": "lake-manifest.json",
   "inputRev": "v0.0.42",
   "inherited": false,
   "configFile": "lakefile.lean"},
  {"url": "https://github.com/leanprover/lean4-cli",
   "type": "git",
   "subDir": null,
   "scope": "",
   "rev": "2cf1030dc2ae6b3632c84a09350b675ef3e347d0",
   "name": "Cli",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/import-graph",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "fb7841a6f4fb389ec0e47dd4677844d49906af3c",
   "name": "importGraph",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": false,
   "configFile": "lakefile.toml"}],
 "name": "mathlib",
 "lakeDir": ".lake"}
"""
    after = b"""
{"version": "1.1.0",
 "packagesDir": ".lake/packages",
 "packages":
 [{"url": "https://github.com/leanprover-community/batteries",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "46fed98b5cac2b1ea64e363b420c382ed1af0d85",
   "name": "batteries",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": false,
   "configFile": "lakefile.lean"},
  {"url": "https://github.com/leanprover-community/quote4",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "2c8ae451ce9ffc83554322b14437159c1a9703f9",
   "name": "Qq",
   "manifestFile": "lake-manifest.json",
   "inputRev": "master",
   "inherited": false,
   "configFile": "lakefile.lean"},
  {"url": "https://github.com/leanprover-community/aesop",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "e5e4f1e9385f5a636cd95f7b5833d9ba7907115c",
   "name": "aesop",
   "manifestFile": "lake-manifest.json",
   "inputRev": "master",
   "inherited": false,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/ProofWidgets4",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "eb08eee94098fe530ccd6d8751a86fe405473d4c",
   "name": "proofwidgets",
   "manifestFile": "lake-manifest.json",
   "inputRev": "v0.0.42",
   "inherited": false,
   "configFile": "lakefile.lean"},
  {"url": "https://github.com/leanprover-community/import---graph",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "fb7841a6f4fb389ec0e47dd4677844d49906af3c",
   "name": "importGraph",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": false,
   "configFile": "lakefile.toml"}],
 "name": "mathlib",
 "lakeDir": ".lake"}
"""
    with contextlib.redirect_stdout(io.StringIO()) as f:
        compare_manifests(before, after)
    s = f.getvalue()
    expected = """\
Package Cli removed at commit [2cf1030dc2ae6b3632c84a09350b675ef3e347d0](https://github.com/leanprover/lean4-cli/tree/2cf1030dc2ae6b3632c84a09350b675ef3e347d0)
Package Qq added at commit [2c8ae451ce9ffc83554322b14437159c1a9703f9](https://github.com/leanprover-community/quote4/tree/2c8ae451ce9ffc83554322b14437159c1a9703f9)
Package aesop moved from commit [bea1488cd9a74883511471a6d3fa954a3ac40809 to e5e4f1e9385f5a636cd95f7b5833d9ba7907115c](https://github.com/leanprover-community/aesop/compare/bea1488cd9a74883511471a6d3fa954a3ac40809..e5e4f1e9385f5a636cd95f7b5833d9ba7907115c)
Package batteries unchanged
Package importGraph moved from commit [fb7841a6f4fb389ec0e47dd4677844d49906af3c](https://github.com/leanprover-community/import-graph/tree/fb7841a6f4fb389ec0e47dd4677844d49906af3c) to [fb7841a6f4fb389ec0e47dd4677844d49906af3c](https://github.com/leanprover-community/import---graph/tree/fb7841a6f4fb389ec0e47dd4677844d49906af3c)
Package proofwidgets unchanged
"""
    assert s == expected

if __name__ == "__main__":
    print(sys.argv)
    if sys.argv[1:] == ["--test"]:
        test()
    else:
        if len(sys.argv) < 2:
            print("Expected arguments revisionBefore, revisionAfter")
            sys.exit(1)
        main(*sys.argv[1:])
