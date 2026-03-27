from util import ReleaseRepo

ALL: list[ReleaseRepo] = []
BY_FULL_NAME: dict[str, ReleaseRepo] = {}


def _register(repo: ReleaseRepo) -> None:
    ALL.append(repo)
    BY_FULL_NAME[repo.full_name] = repo


##################
## Repositories ##
##################

LEAN4 = ReleaseRepo(
    owner="leanprover",
    name="lean4",
)  # Don't register this repo!

LEAN4_NIGHTLY = ReleaseRepo(
    owner="leanprover",
    name="lean4-nightly",
)  # Don't register this repo!


BATTERIES = ReleaseRepo(
    owner="leanprover-community",
    name="batteries",
    toolchain_tag=True,
    stable_branch=True,
    bump_branch=True,
)
_register(BATTERIES)

AESOP = ReleaseRepo(
    owner="leanprover-community",
    name="aesop",
    toolchain_tag=True,
    stable_branch=True,
    dependencies=[
        BATTERIES,
    ],
)
_register(AESOP)

LEAN4_CLI = ReleaseRepo(
    owner="leanprover",
    name="lean4-cli",
    toolchain_tag=True,
)
_register(LEAN4_CLI)

IMPORT_GRAPH = ReleaseRepo(
    owner="leanprover-community",
    name="import-graph",
    toolchain_tag=True,
    dependencies=[
        LEAN4_CLI,
    ],
)
_register(IMPORT_GRAPH)

PLAUSIBLE = ReleaseRepo(
    owner="leanprover-community",
    name="plausible",
    toolchain_tag=True,
)
_register(PLAUSIBLE)

PROOFWIDGETS4 = ReleaseRepo(
    owner="leanprover-community",
    name="ProofWidgets4",
)
_register(PROOFWIDGETS4)

MATHLIB4 = ReleaseRepo(
    owner="leanprover-community",
    name="mathlib4",
    nightly=ReleaseRepo(owner="leanprover-community", name="mathlib4-nightly-testing"),
    toolchain_tag=True,
    stable_branch=True,
    bump_branch=True,
    dependencies=[
        AESOP,
        BATTERIES,
        IMPORT_GRAPH,
        LEAN4_CLI,
        PLAUSIBLE,
        PROOFWIDGETS4,
    ],
)
_register(MATHLIB4)

CSLIB = ReleaseRepo(
    owner="leanprover",
    name="cslib",
    toolchain_tag=True,
    stable_branch=True,
    bump_branch=True,
    dependencies=[
        MATHLIB4,
    ],
)
_register(CSLIB)

REPL = ReleaseRepo(
    owner="leanprover-community",
    name="repl",
    toolchain_tag=True,
    stable_branch=True,
    dependencies=[
        MATHLIB4,
    ],
)
_register(REPL)

VERSO = ReleaseRepo(
    owner="leanprover",
    name="verso",
    toolchain_tag=True,
    dependencies=[
        MATHLIB4,  # Benchmarks
        PLAUSIBLE,
    ],
)
_register(VERSO)

REFERENCE_MANUAL = ReleaseRepo(
    owner="leanprover",
    name="reference-manual",
    toolchain_tag=True,
    dependencies=[
        VERSO,
    ],
)
_register(REFERENCE_MANUAL)

VERSO_WEB_COMPONENTS = ReleaseRepo(
    owner="leanprover",
    name="verso-web-components",
    toolchain_tag=True,
    dependencies=[
        VERSO,
    ],
)
_register(VERSO_WEB_COMPONENTS)

LEAN_FRO_ORG = ReleaseRepo(
    owner="leanprover",
    name="lean-fro.org",
    dependencies=[
        VERSO_WEB_COMPONENTS,
    ],
)
_register(LEAN_FRO_ORG)

LEAN4_UNICODE_BASIC = ReleaseRepo(
    owner="fgdorais",
    name="lean4-unicode-basic",
)
_register(LEAN4_UNICODE_BASIC)

BIBTEX_QUERY = ReleaseRepo(
    owner="dupuisf",
    name="BibtexQuery",
    toolchain_tag=True,
    dependencies=[
        LEAN4_UNICODE_BASIC,
    ],
)
_register(BIBTEX_QUERY)

DOC_GEN4 = ReleaseRepo(
    owner="leanprover",
    name="doc-gen4",
    toolchain_tag=True,
    dependencies=[
        BIBTEX_QUERY,
        LEAN4_CLI,
        MATHLIB4,
    ],
)
_register(DOC_GEN4)

COMPARATOR = ReleaseRepo(
    owner="leanprover",
    name="comparator",
    toolchain_tag=True,
)
_register(COMPARATOR)

LEAN4EXPORT = ReleaseRepo(
    owner="leanprover",
    name="lean4export",
    toolchain_tag=True,
)
_register(LEAN4EXPORT)

QUOTE4 = ReleaseRepo(
    owner="leanprover-community",
    name="quote4",
    toolchain_tag=True,
    stable_branch=True,
)
_register(QUOTE4)


###################
## Visualization ##
###################


def print_graphviz_dot() -> None:
    print("digraph G {")
    print("  rankdir=LR;")
    for repo in sorted(ALL, key=lambda r: r.full_name):
        print(f'  "{repo.full_name}"')
        for dep in repo.dependencies:
            print(f'  "{dep.full_name}" -> "{repo.full_name}"')
    print("}")


if __name__ == "__main__":
    print_graphviz_dot()
