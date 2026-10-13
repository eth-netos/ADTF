## Code comments

Do not write code comments that just narrate what's already clear from the code. Only add comments to clarify what's not clear immediately.
Do not write comments that read like a response to a particular prompt. Instead, make sure each comment makes sense on its own.
If the name of a definition contains an abbreviation, expand the abbreviation in a doc comment.

## Warnings

When checking the output of build commands, do not only check for success/failure, but also read the warnings. Fix all warnings that have a simple reasonable fix, and tell the user about remaining warnings for which there's no simple fix.

## git

Creating a pretty git history is *not* a goal in this project. The goal is to create an *accurate* history that includes everything that was tried, including failed experiments.
Therefore, never rewrite git history, and never rebase, but merge instead.

For each prompt that causes you to write code, create at least one commit. It is ok to create commits that don't compile or that fail tests, in order to document what was tried. Mark such commits by prefixing their commit message with `[broken]`. Before creating commits that you think should work, double check by running the build and tests. 

Do not try to imitate the git commit message format of previous commits. Instead, always use the following format: 

* A summary line
* An empty line as per git conventions
* A line `Prompt:`
* An empty line
* The prompt, verbatim, but wrapped at 72 chars
* An empty line
* A line `Outcome:`
* An empty line
* A brief summary of what you did, wrapped at 72 chars 
* An empty line
* A Co-authored-by trailer where you credit yourself, including the model name and model version number
