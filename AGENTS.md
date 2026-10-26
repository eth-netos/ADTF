## Code comments

Do not write code comments that just narrate what's already clear from the code. Only add comments to clarify what's not clear immediately.
Do not write comments that read like a response to a particular prompt. Instead, make sure each comment makes sense on its own.
If the name of a definition contains an abbreviation, expand the abbreviation in a doc comment.

## Distinguish between code generators, agents, and humans

When talking about what you are doing, remember that you are an agent, and use terminology accordingly.
You are not a human. You do not have hands, so you cannot create handwritten code, and "manual" comes from the Latin word "manus", meaning "hand", so you also cannot produce any "manually written code" etc.
Sometimes you write code generators, and you need to distinguish between code produced by the code generator and code that cannot be produced by the code generator.
Instead of "hand-written code" or "manually written code", say "code that cannot be produced by the code generator".
Other phrases that are safe to use: "code produced by a code generator", "code produced by the xyz backend", "agent-written code".

## Code formatting

When you start a new file, make its lines at most 80 characters wide.
When editing existing files, adapt to the line width used there.

## Respect decisions from human commits

Before coding, read the output of

```
git log -n5 --format="%h %an <%ae> %(trailers:key=Co-authored-by,valueonly=true,separator= )"
```

to see the authors and co-authors of the last five commits.
If there are commits without any AI co-authors, read these commits using `git show <HASH>`, and treat the changes you see as authoritative design decisions you have to respect.
If you think that ignoring them would be beneficial, first ask the user.

## Warnings

When checking the output of build commands, do not only check for success/failure, but also read the warnings. Fix all warnings that have a simple reasonable fix, and tell the user about remaining warnings for which there's no simple fix.

## Rust

Before committing, run `cargo build --all-targets` and use cargo to run those test files that you think matter for the changes you made.

## Cross-language style guide

**Tuples:** Use destructuring syntax instead of generic numbered accessors if it makes the code shorter or more readable. For instance, in Lean, instead of `(fun foo_and_bar => foo_and_bar.1 + foo_and_bar.2)`, write `(fun (foo, bar) => foo + bar)`.

## git

Creating a pretty git history is *not* a goal in this project. The goal is to create an *accurate* history that includes everything that was tried, including failed experiments.
Therefore, never rewrite git history, and never rebase, but merge instead.

For each prompt that causes you to write code, create at least one commit. It is ok to create commits that don't compile or that fail tests, in order to document what was tried. Mark such commits by prefixing their commit message with `[broken]`. Before creating commits that you think should work, double check by running the build and tests. 

Do not try to imitate the git commit message format of previous commits. Instead, always use the following format: 

* A summary line
* An empty line as per git conventions
* A line `Prompt:`
* An empty line
* The prompt, verbatim, but wrapped at 72 chars. If several tasks were given in one prompt and the user asked for separate commits, only include the prompt of the current task. If the current commit is the result of several prompts, include all of them, and add a line `Prompt:` and an empty line before each prompt. Also add an empty line after each prompt
* A line `Outcome:`
* An empty line
* A brief summary of what you did, wrapped at 72 chars, at most 12 lines long
* An empty line
* How much wall-clock time it took you to solve the task of this commit, on a line in `Time spent (excl initial prompt reading & final summary): %Hh %Mmin %Ss` format. Before starting a new task, record the current time, and before committing, calculate the difference using a tool.
* An empty line
* A Co-authored-by trailer where you credit yourself, including the model name and model version number

Commit messages often contain backticks and `$`, which the shell expands in double-quoted strings and in unquoted here-documents (`<<EOF`), silently dropping text or running commands. So write the message to a file with a file-writing tool (not the shell), or with a quoted here-document (`<<'EOF'`), and commit with `git commit -F <file>`.

### git submodules

Before committing, read `git status` to know what's going on, and pay attention to the submodules. If the changes you are about to commit depend on the contents of submodules, first make the necessary submodule commit(s). Then, in the parent repo, there should be no more "modified content" status, but maybe some "new commits" status for submodules. Also `git add` the submodules with changes relevant for the current commit, so that it is always clear from the git history against what submodule contents the parent's code was tested.
If a task only made changes in a submodule and the only change in the parent module is that the hash of the submodule changed, do not make a commit in the parent module.
