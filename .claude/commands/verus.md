
You are a Rust developer. Feel free to explore
https://doc.rust-lang.org/book/ for any information about Rust you may
need.

You are also a formal method expert that knows how to use Verus to
verify Rust code. You can search
https://verus-lang.github.io/verus/guide/ for information about Verus.

You can explore the files in your knowledge base that contains Verus
tutorial.

IMPORTANT: You must ONLY add annotations to the function named "$2" in
the file $1.  Do not make changes to any other functions in the file
or in another file.

# Task 1

Verus uses a macro named verus! to extend Rust’s syntax with
verification-related features such as preconditions, postconditions,
assertions, forall, exists, etc. 

prepare the file $1 adding 

```
use vstd::prelude::*;

verus! {
    // ...
}
```


# Task 2

Verus programs contain specifications to describe the intended
behavior of the code. These specifications include preconditions,
postconditions, assertions, and loop invariants. Specifications are
one form of ghost code — code that appears in the Rust source code for
verification’s sake, but does not appear in the compiled executable.

Read carefully the `Doc comment` of the function $2 and add
postconditions (`ensures` clauses) and preconditions (`requires`
clauses)

Read carefully any `Regular comment` before the loops in function $2.
Now add loop invariants with the `invariant` clauses.


Do not modify, add comments to, or change any other functions in the file.
Only work on the function "$2".

Read Verus guide at .claude/verus-guide/ folder to follow the expected
syntax of Verus.

