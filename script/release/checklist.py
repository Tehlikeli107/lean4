from argparse import ArgumentParser, Namespace
from dataclasses import dataclass
from pathlib import Path

import repos
from github import Github, UnknownObjectException
from github.GitRef import GitRef
from github.GitRelease import GitRelease
from github.PullRequest import PullRequest
from rich import print
from rich.markup import escape as e

import util
from util import Checklist, LocalRepo, ReleaseRepo, Version


@dataclass
class Config:
    version: Version
    interactive: bool
    fast: bool
    github: Github


class RepoChecker:
    def __init__(self, config: Config, rrepo: ReleaseRepo) -> None:
        self.config = config
        self.cl = Checklist()

        self.rrepo = rrepo
        self.grepo = self.github.get_repo(self.rrepo.full_name)
        self.lrepo = self.rrepo.local

    @property
    def github(self) -> Github:
        return self.config.github

    @property
    def version(self) -> Version:
        return self.config.version

    def prompt(self, message: str) -> bool:
        if not self.config.interactive:
            return False
        return util.prompt(message) == "y"

    def check_pr_closed(self, pr: PullRequest, what: str, required: bool) -> None:
        if pr.state == "open":
            if required:
                self.cl.blocked(f"{what} found: {util.fmt_pr(pr)}")
            else:
                self.cl.wait(f"{what} found: {util.fmt_pr(pr)}")
            return

        if pr.merged:
            self.cl.success(f"{what} merged: {util.fmt_pr(pr)}")
        else:
            self.cl.success(f"{what} closed: {util.fmt_pr(pr)}")

        try:
            pr.head.repo.get_git_ref(f"heads/{pr.head.ref}")
            self.cl.warn("PR branch has not been deleted")
        except UnknownObjectException:
            self.cl.success("PR branch has been deleted")


class DownstreamChecker(RepoChecker):
    def __init__(self, config: Config, rrepo: ReleaseRepo, completed: set[str]) -> None:
        super().__init__(config=config, rrepo=rrepo)
        self.completed = completed

    def check_dependencies_completed(self) -> None:
        for dep in self.rrepo.dependencies:
            if dep.full_name not in self.completed:
                self.cl.wait(
                    f"Awaiting completion of dependency [b]{e(dep.full_name)}[/b]"
                )
        self.cl.ensure_success()

    def check_toolchain(self) -> bool:
        expected = util.get_toolchain_for(self.version)
        actual = util.get_toolchain(self.grepo, self.grepo.default_branch)

        if expected == actual:
            self.cl.success(f"Toolchain is [b]{e(actual)}[/b]")
            return True
        else:
            self.cl.fail(f"Toolchain is [b]{e(actual)}[/b]")
            return False

    def _bump_toolchain(self, path: Path) -> None:
        util.set_toolchain(path, self.version.tag)

    def _bump_toolchain_deps(self, path: Path) -> None:
        lakefile = path / "lakefile.toml"
        if not lakefile.exists():
            lakefile = path / "lakefile.lean"

        util.edit(
            lakefile,
            r'rev = "v4\.[0-9]+(\.[0-9]+)?(-rc[0-9]+)?"',
            f'rev = "{self.version}"',
        )

        util.run("lake", "update", cwd=path)

    def _bump_toolchain_mathlib4(self, lrepo: LocalRepo) -> None:
        pw = self.github.get_repo(repos.PROOFWIDGETS4.full_name)
        tag = util.get_proofwidgets_release_for(pw, self.version)
        if not tag:
            raise SystemExit(1)

        # For both normal and rc1 PRs
        util.edit(
            lrepo.path / "lakefile.lean",
            r'"proofwidgets" @ git ".*"',
            f'"proofwidgets" @ git "{tag.name}"',
        )

        # For rc1 PRs
        util.edit(
            lrepo.path / "lakefile.lean",
            r' @ git "nightly-testing"',
            f' @ git "{self.version}"',
        )

        self._bump_toolchain_deps(lrepo.path)

    def _bump_toolchain_repl(self, lrepo: LocalRepo) -> None:
        self._bump_toolchain_deps(lrepo.path)

        mathlib = lrepo.path / "test" / "Mathlib"
        self._bump_toolchain(mathlib)
        self._bump_toolchain_deps(mathlib)

        if util.prompt("Run tests?") == "y":
            try:
                util.run("./test.sh", cwd=lrepo.path)
                print("#####################")
                print("## Tests succeeded ##")
                print("#####################")
            except SystemExit as e:
                print("###################")
                print("## Tests failed! ##")
                print("###################")
                raise e

    def _bump_toolchain_verso(self, lrepo: LocalRepo) -> None:
        self._bump_toolchain_deps(lrepo.path)
        util.run("./update-subverso.sh", cwd=lrepo.path)

    def _bump_toolchain_reference_manual(self, lrepo: LocalRepo) -> None:
        self._bump_toolchain_deps(lrepo.path)

        lean4 = self.github.get_repo(repos.LEAN4.full_name)
        release = lean4.get_release(self.version.tag)
        util.set_release_notes_title(lrepo, self.version, release)

    def _bump_toolchain_lean_fro_org(self, lrepo: LocalRepo) -> None:
        self._bump_toolchain_deps(lrepo.path)

        hero = lrepo.path / "examples" / "hero"
        self._bump_toolchain(hero)
        self._bump_toolchain_deps(hero)

        util.run("scripts/update.sh", cwd=lrepo.path)

    def _bump_toolchain_bibtex_query(self, lrepo: LocalRepo) -> None:
        lub = self.github.get_repo(repos.LEAN4_UNICODE_BASIC.full_name)
        tag = util.get_lean_unicode_basic_release_for(lub, self.version)
        if not tag:
            raise SystemExit(1)

        util.edit(
            lrepo.path / "lakefile.toml",
            r'(name = "UnicodeBasic"[\s\S]*?rev =) ".+?"',
            rf'\1 "{tag}"',
        )

        self._bump_toolchain_deps(lrepo.path)

    def _bump_toolchain_in_worktree(self, rrepo: ReleaseRepo, lrepo: LocalRepo) -> None:
        self._bump_toolchain(lrepo.path)

        # Special cases
        if rrepo.full_name == repos.MATHLIB4.full_name:
            self._bump_toolchain_mathlib4(lrepo)
        elif rrepo.full_name == repos.REPL.full_name:
            self._bump_toolchain_repl(lrepo)
        elif rrepo.full_name == repos.VERSO.full_name:
            self._bump_toolchain_verso(lrepo)
        elif rrepo.full_name == repos.REFERENCE_MANUAL.full_name:
            self._bump_toolchain_reference_manual(lrepo)
        elif rrepo.full_name == repos.LEAN_FRO_ORG.full_name:
            self._bump_toolchain_lean_fro_org(lrepo)
        elif rrepo.full_name == repos.BIBTEX_QUERY.full_name:
            self._bump_toolchain_bibtex_query(lrepo)
        elif rrepo.dependencies:
            self._bump_toolchain_deps(lrepo.path)

    def check_bump_pr(self, required: bool) -> None:
        what = f"Bump PR for [b]{self.version}[/b]"
        use_bump_branch = self.rrepo.bump_branch and self.version.rc == 1

        head = f"bump-to-{self.version}"
        base = self.grepo.default_branch
        if use_bump_branch:
            head = util.get_bump_branch(self.version)

        # Won't find anything if self.rrepo.nightly
        pr = util.find_pr(self.grepo, head=head, base=base)
        if pr:
            self.check_pr_closed(pr, what, required)
            return
        if not required:
            self.cl.success(f"{what} not found")
            return
        if not self.prompt(f"{what} not found. Create?"):
            self.cl.fatal(f"{what} not found")

        #                         source           head                base
        # Normally:               origin/main   -> origin/bump-to-* -> origin/main
        # Nightly:                upstream/main -> origin/bump-to-* -> upstream/main
        # RC1 w/ bump branch:                      origin/bump/*    -> origin/main
        # Nightly w/ bump branch:                  origin/bump/*    -> upstream/main

        # Step 0: Set up local repo
        if self.rrepo.nightly:
            lrepo = self.rrepo.nightly.local
            lrepo.prepare(upstream=self.rrepo)
            source_remote = "upstream"
        else:
            lrepo = self.lrepo
            lrepo.prepare()
            source_remote = "origin"

        # Step 1: Switch to branch or create branch
        if use_bump_branch:
            lrepo.switch(head)
        else:
            lrepo.create_branch(head, remote=source_remote)

        # Step 2: Bump toolchain and do repo-specific stuff as required
        message = util.get_toolchain_bump_message(self.version)
        self._bump_toolchain_in_worktree(self.rrepo, lrepo)
        lrepo.commit(message)

        # Step 3: Push branch
        if not self.prompt(f"Push branch [b]{e(head)}[/b]?"):
            self.cl.fatal(f"{what} not found")
        lrepo.push(head)

        # Step 4: Create PR

        # Mathlib bump PRs are opened from the nightly-testing repo, which
        # pygithub doesn't support because both belong to the same organization:
        # https://github.com/PyGithub/PyGithub/issues/2942
        # So we just give the user a link instead
        if self.version.rc == 1 and self.rrepo.nightly:
            url = util.create_pr_url(
                base=self.rrepo,
                base_branch=base,
                head=self.rrepo.nightly,
                head_branch=head,
                title=message,
            )
            self.cl.blocked(f"[u link={url}]Create mathlib bump PR manually[/]")
            return

        if not self.prompt(f"Create PR for branch [b]{e(head)}[/b]?"):
            self.cl.fatal(f"{what} not found")
        pr = util.create_pr(self.grepo, head=head, base=base, title=message)
        self.cl.blocked(f"{what} created: {util.fmt_pr(pr)}")

    def check_next_bump_branch(self) -> None:
        if not self.rrepo.bump_branch:
            return

        grepo = self.grepo
        if self.rrepo.nightly:
            grepo = self.github.get_repo(self.rrepo.nightly.full_name)

        branch_name = util.get_bump_branch(self.version.next)
        what = f"Bump branch [b]{e(branch_name)}[/b]"
        try:
            grepo.get_branch(branch_name)
            self.cl.success(f"{what} exists")
            return
        except UnknownObjectException:
            pass

        if not self.prompt(f"{what} not found. Create?"):
            self.cl.fail(f"{what} not found")
            return

        gnightly = self.github.get_repo(repos.LEAN4_NIGHTLY.full_name)
        latest_nightly_tag = util.get_latest_nightly_tag(gnightly)

        if self.rrepo.nightly:
            lrepo = self.rrepo.nightly.local
            lrepo.prepare(upstream=self.rrepo)
        else:
            lrepo = self.lrepo
            lrepo.prepare()

        lrepo.create_branch(branch_name)
        util.set_toolchain(lrepo.path, latest_nightly_tag.name)

        message = f"chore: bump toolchain to {latest_nightly_tag.name}"
        lrepo.commit(message)

        if not self.prompt(f"Push branch [b]{e(branch_name)}[/b]?"):
            self.cl.fail(f"{what} not found")
            return
        lrepo.push(branch_name)
        self.cl.success(f"{what} created")

    def check_toolchain_tag(self) -> GitRef | None:
        if not self.rrepo.toolchain_tag:
            return

        tag_name = self.version.tag
        what = f"Toolchain tag [b]{tag_name}[/b]"

        try:
            tag = self.grepo.get_git_ref(f"tags/{tag_name}")
            self.cl.success(f"{what} exists")
            return tag
        except UnknownObjectException:
            pass

        if not self.prompt(f"{what} not found. Create?"):
            self.cl.fail(f"{what} not found")
            return

        self.lrepo.prepare()
        bump_sha = util.find_merged_toolchain_bump_sha(self.lrepo, self.version)
        self.lrepo.create_tag(tag_name, bump_sha)

        if not self.prompt(f"Push tag [b]{tag_name}[/b]?"):
            self.cl.fatal(f"{what} does not exist")
        self.lrepo.push(tag_name, upstream=False)

        tag = self.grepo.get_git_ref(f"tags/{tag_name}")
        self.cl.success(f"{what} created")
        return tag

    def check_stable_branch_points_to_toolchain_tag(self, tag: GitRef) -> None:
        if not self.rrepo.stable_branch:
            return
        if not self.version.is_stable:
            return

        what = "Stable branch"

        branch = self.grepo.get_branch("stable")
        if branch.commit.sha == tag.object.sha:
            self.cl.success(f"{what} points to toolchain tag")
            return

        if not self.prompt(f"{what} does not point to toolchain tag. Update?"):
            self.cl.fail(f"{what} does not point to toolchain tag")
            return

        self.lrepo.prepare()
        self.lrepo.switch("stable")
        self.lrepo.git("merge", "--ff-only", self.version.tag)

        if not self.prompt("Push branch [b]stable[/b] to origin?"):
            self.cl.fail(f"{what} does not point to toolchain tag")
            return

        self.lrepo.push("stable")
        self.cl.success(f"{what} updated to point to toolchain tag")

    def check_proofwidgets_release(self) -> None:
        if self.rrepo.full_name != repos.PROOFWIDGETS4.full_name:
            return

        what = f"Proofwidgets release with toolchain {self.version}"

        tag = util.get_proofwidgets_release_for(self.grepo, self.version)
        if tag:
            self.cl.success(f"{what} found: [b]{e(tag.name)}[/b]")
            return

        tag_name = util.get_next_proofwidgets_release(self.grepo)
        if not self.prompt(f"{what} not found. Create [b]{e(tag_name)}[/b]?"):
            self.cl.fail(f"{what} not found")
            return

        self.lrepo.prepare()
        bump_sha = util.find_merged_toolchain_bump_sha(self.lrepo, self.version)
        self.lrepo.create_tag(tag_name, bump_sha)

        if not self.prompt(f"Push tag [b]{tag_name}[/b]?"):
            self.cl.fatal(f"{what} does not exist")
        self.lrepo.push(tag_name, upstream=False)
        self.cl.success(f"{what} created")

    def check_mathlib4_version_tags(self) -> None:
        if self.rrepo.full_name != repos.MATHLIB4.full_name:
            return
        if self.config.fast:
            return

        # At this point, the PR has been merged
        self.lrepo.prepare()
        self.lrepo.switch(self.grepo.default_branch)

        script = "scripts/verify_version_tags.py"
        try:
            self.lrepo.run("python", script, self.version.tag)
            self.cl.success(f"Version tags verified by [b]{e(script)}[/b]")
        except Exception:
            self.cl.fatal(f"Version tag verification by [b]{e(script)}[/b] failed")

    def check(self) -> None:
        self.check_dependencies_completed()
        toolchain = self.check_toolchain()

        # Special cases for special repos
        if not toolchain:
            if self.rrepo.full_name == repos.LEAN4_UNICODE_BASIC.full_name:
                self.cl.fatal("Repo must be updated manually")

        self.check_bump_pr(required=not toolchain)
        self.check_next_bump_branch()

        toolchain_tag = self.check_toolchain_tag()
        if toolchain_tag:
            self.check_stable_branch_points_to_toolchain_tag(toolchain_tag)

        self.check_proofwidgets_release()
        if toolchain:
            self.check_mathlib4_version_tags()

        self.cl.ensure_success()


class LeanChecker(RepoChecker):
    def __init__(self, config: Config) -> None:
        super().__init__(config=config, rrepo=repos.LEAN4)

    def _check_label_exists(
        self, name: str, color: str, description: str | None = None
    ) -> None:
        what = f"Label [b]{e(name)}[/b]"

        try:
            self.grepo.get_label(name)
            self.cl.success(f"{what} exists")
            return
        except UnknownObjectException:
            pass

        if not self.prompt(f"{what} does not exist. Create?"):
            self.cl.fail(f"{what} does not exist")
            return

        if description is None:
            self.grepo.create_label(name=name, color=color)
        else:
            self.grepo.create_label(name=name, color=color, description=description)
        self.cl.success(f"{what} created")

    def check_backport_label_exists(self, version: Version) -> None:
        self._check_label_exists(
            name=util.get_backport_label(version),
            color="1d76db",
        )

    def check_blocking_label_exists(self, version: Version) -> None:
        self._check_label_exists(
            name=util.get_blocking_label(version),
            color="b60205",
            description=f"Blocks the next {version.base} release candidate or release from being published.",
        )

    def check_release_branch_exists(self) -> None:
        branch_name = util.get_releases_branch(self.version)
        what = f"Release branch [b]{e(branch_name)}[/b]"

        try:
            self.grepo.get_branch(branch_name)
            self.cl.success(f"{what} exists")
            return
        except UnknownObjectException:
            pass

        if not self.prompt(f"{what} does not exist. Create?"):
            self.cl.fatal(f"{what} does not exist")

        self.lrepo.prepare()
        self.lrepo.create_branch(branch_name)

        if not self.prompt(f"Push branch [b]{e(branch_name)}[/b]?"):
            self.cl.fatal(f"{what} does not exist")
        self.lrepo.push(branch_name)

        self.grepo.get_branch(branch_name)
        self.cl.success(f"{what} created")

    def check_release_branch_cmake_version(self) -> None:
        branch_name = util.get_releases_branch(self.version)
        what = f"CMake version settings on [b]{e(branch_name)}[/b]"

        version, is_release = util.get_cmake_version(self.grepo, branch_name)
        if version == self.version.base and is_release:
            self.cl.success(f"{what} are correct")
            return

        if not self.prompt(f"{what} are incorrect. Update?"):
            self.cl.fail(f"{what} are incorrect")
            return

        self.lrepo.prepare()
        self.lrepo.switch(branch_name)
        util.set_cmake_version(self.lrepo, self.version.base, is_release=True)
        self.lrepo.commit("chore: prepare release")

        if not self.prompt(f"Push branch [b]{e(branch_name)}[/b]?"):
            self.cl.fail(f"{what} are incorrect")
            return
        self.lrepo.push(branch_name)
        self.cl.success(f"{what} updated")

    def check_master_branch_cmake_version(self) -> bool:
        branch_name = self.grepo.default_branch
        what = f"CMake version settings on [b]{e(branch_name)}[/b]"

        version, is_release = util.get_cmake_version(self.grepo, branch_name)
        if version == self.version.next and not is_release:
            self.cl.success(f"{what} are correct")
            return True
        else:
            self.cl.fail(f"{what} are incorrect")
            return False

    def check_dev_cycle_pr(self, required: bool) -> None:
        head = self.grepo.default_branch
        base = f"dev-cycle-{self.version.next}"
        what = f"Dev cycle PR for [b]{self.version.next}[/b]"

        pr = util.find_pr(self.grepo, head=head, base=base)
        if pr:
            self.check_pr_closed(pr, what, required)
            return
        if not required:
            self.cl.success(f"{what} not found")
            return
        if not self.prompt(f"{what} not found. Create?"):
            self.cl.fail(f"{what} not found")
            return

        message = f"chore: prepare development cycle for {self.version.next}"
        self.lrepo.prepare()
        self.lrepo.create_branch(base, head)
        util.set_cmake_version(self.lrepo, self.version.next, is_release=False)
        self.lrepo.commit(message)

        if not self.prompt(f"Push branch [b]{e(head)}[/b]?"):
            self.cl.fail(f"{what} are incorrect")
            return
        self.lrepo.push(head)

        if not self.prompt(f"Create PR for branch [b]{e(head)}[/b]?"):
            self.cl.fail(f"{what} are incorrect")
            return
        pr = util.create_pr(self.grepo, head=head, base=base, title=message)
        self.cl.success(f"{what} created: {util.fmt_pr(pr)}")

    def _check_no_open_prs_labeled(self, label: str) -> None:
        success = True
        for issue in self.grepo.get_issues(state="open", labels=[label]):
            kind = "PR" if issue.pull_request else "issue"
            self.cl.fail(f"Found {kind} {util.fmt_pr(issue)} labeled [b]{e(label)}[/b]")
            success = False
        if success:
            self.cl.success(f"Found no open PRs labeled [b]{e(label)}[/b]")

    def check_no_open_prs_labeled_backport(self) -> None:
        self._check_no_open_prs_labeled(util.get_backport_label(self.version))

    def check_no_open_prs_labeled_blocking(self) -> None:
        self._check_no_open_prs_labeled(util.get_blocking_label(self.version))

    def check_no_open_backport_prs(self) -> None:
        base = util.get_releases_branch(self.version)
        success = True
        for pr in self.grepo.get_pulls(state="open", base=base):
            if "backport" in pr.title.lower():
                self.cl.fail(f"Found backport PR #{pr.number} {util.fmt_pr(pr)}")
                success = False
        if success:
            self.cl.success("Found no open backport PRs")

    def check_release_tag(self) -> GitRef:
        tag_name = self.version.tag
        what = f"Tag [b]{tag_name}[/b]"

        try:
            ref = self.grepo.get_git_ref(f"tags/{tag_name}")
            self.cl.success(f"{what} exists")
            return ref
        except UnknownObjectException:
            pass

        if not self.prompt(f"{what} does not exist. Create?"):
            self.cl.fatal(f"{what} does not exist")

        self.lrepo.prepare()
        self.lrepo.create_tag(tag_name, util.get_releases_branch(self.version))

        if not self.prompt(f"Push tag [b]{tag_name}[/b]?"):
            self.cl.fatal(f"{what} does not exist")
        self.lrepo.push(tag_name, upstream=False)

        tag = self.grepo.get_git_ref(f"tags/{tag_name}")
        self.cl.success(f"{what} created")
        return tag

    def check_release_ci(self, release_tag: GitRef) -> None:
        tag_sha = release_tag.object.sha
        runs = self.grepo.get_workflow_runs(event="push", head_sha=tag_sha).get_page(0)
        if len(runs) == 0:
            self.cl.fail("Release workflow run not found")
            return

        run = runs[0]
        what = f"[b u link={run.html_url}]Release workflow run {run.id}[/]"

        if not run.conclusion:
            self.cl.blocked(f"{what} is still running")
        if run.conclusion != "success":
            self.cl.fatal(f"{what} failed")
        self.cl.success(f"{what} finished")

    def check_release_page(self) -> GitRelease:
        what = f"Release page for [b]{self.version.tag}[/b]"
        try:
            release = self.grepo.get_release(self.version.tag)
            self.cl.success(f"{what} exists")
            return release
        except UnknownObjectException:
            self.cl.blocked(f"{what} not found")

    def check_reference_manual_title(self, release: GitRelease) -> None:
        what = f"Release log for [b]{self.version.base}[/b]"
        rrepo = self.github.get_repo(repos.REFERENCE_MANUAL.full_name)

        expected = util.get_release_notes_title_for(self.version, release)
        actual = util.get_release_notes_title(rrepo, self.version)
        if actual is None:
            self.cl.fail(f"{what} not found")
            return

        if actual == expected:
            self.cl.success(f"{what} has title [b]{e(actual)}[/b]")
        else:
            self.cl.fail(f"{what} has title [b]{e(actual)}[/b]")

    def check(self) -> None:
        self.cl.section("Prepare release cycle")
        self.check_backport_label_exists(self.version)
        self.check_blocking_label_exists(self.version)
        self.check_blocking_label_exists(self.version.next)
        self.check_release_branch_exists()
        self.check_release_branch_cmake_version()
        cmake_version = self.check_master_branch_cmake_version()
        self.check_dev_cycle_pr(required=not cmake_version)

        self.cl.section("Release")
        self.check_no_open_prs_labeled_backport()
        self.check_no_open_prs_labeled_blocking()
        self.check_no_open_backport_prs()
        release_tag = self.check_release_tag()
        self.check_release_ci(release_tag)
        release = self.check_release_page()
        self.check_reference_manual_title(release)

        completed: set[str] = set()
        for drepo in repos.ALL:
            self.cl.section(f"[u link={drepo.url}]{e(drepo.full_name)}[/u link]")
            dchecker = DownstreamChecker(
                config=self.config, rrepo=drepo, completed=completed
            )
            try:
                dchecker.check()
                completed.add(drepo.full_name)
            except SystemExit:
                self.cl.failed = True

        self.cl.ensure_success()


def main(version: Version, interactive: bool = False, fast: bool = False) -> None:
    util.initialize_rich()
    github = util.get_github_instance()
    config = Config(version=version, interactive=interactive, fast=fast, github=github)
    LeanChecker(config=config).check()


class Args(Namespace):
    version: Version
    interactive: bool
    fast: bool


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("version", type=Version.parse)
    parser.add_argument("--interactive", "-i", action="store_true")
    parser.add_argument("--fast", "-f", action="store_true")
    args = parser.parse_args(namespace=Args())
    main(version=args.version, interactive=args.interactive, fast=args.fast)
