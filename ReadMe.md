# Project

This is an implementation of Normalization-By-Evaluation in Lean4 from the ([PDF](Leicester.pdf)) slide notes.

Currently what is formalized is:

- Normalization-By-Eval for Monoid-rewriting (Slides 25-35)

- Normalization-By-Eval for Godel's system T (Slides 62-70)


# Build instructions for Verso-textbook
To build the Verso-textbook documenting the code:

1. Run `lake exe cache get`: 
    
    This makes it so mathlib is quick to build

2. Run `lake build`:

    This builds the `.lake` directory.

3. Copy the code from `_in/textbook/DemoTextbook.lean` and paste it all into `.lake/packages/verso/examples/textbook/DemoTextbook.lean`:

    This is an ugly work-around I did, since I didn't know how to deal with git-submodules (verso is a submodule of my git-repo) and because the .lake directory is git-ignored.
Because of both of these things, I did the easiest workaround for myself: I manually copied the code from  `.lake/packages/verso/examples/textbook/DemoTextbook.lean` and put it in the unused `_in/textbook/DemoTextbook.lean` so git could keep track of my verso-code.
When you build verso in the `lake build` step, it is going to have the example code from the verso-repo. So in this step you are manually replacing the example-code with the verso-code I have written.

4. Run `lake exe demotextbook --output _out/examples/demotextbook`:

    This will take the verso code from `.lake/packages/verso/examples/textbook/DemoTextbook.lean`, build the textbook from it, and put everything in the `_out` directory.

5. Run `python3 -m http.server 8880 --directory _out/examples/demotextbook/html-single &`:

    This creates a local server where you can read the textbook that was built.

6. View the textbook in your browser with `http://localhost:8880/`

