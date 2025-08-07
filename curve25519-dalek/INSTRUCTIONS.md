Your goal is to make `verus --no-cheating src/backend/serial/u64/sub.rs` pass, i.e. not using assume. You may change the pre/post conditions of sub, but ONLY IF THEY'RE WRONG. DO NOT USE THIS TO CHEAT.

Proving `sub` is a hard task, and you may not be able to finish it. But you can at least make an incremental improvement, like:
- discovering that the postconditions of an unproved lemma are untrue given only the preconditions, and hence changing the lemma so it is true
- Planning a proof strategy, trying it out, and leaving a comment with the result
- Replacing an assume with a proof
- Replacing an assume with a proof and a weaker assume

There will be other agents after you with the same goal, so make life easier for them

If there's an assume in a lemma, and you replace that assume with another lemma that uses an assume of the same strength, that's not progress. Don't weasel out like that

You should ultrathink. You may look at the URLs in "Verus docs" in CLAUDE.md (especially for more mathematical properties).

Do not run any "cargo verus" command. The correct command is the one I've given. You can run `verus src/backend/serial/u64/sub.rs` to see how a proof does with assumes. But the actual goal is to make `verus --no-cheating src/backend/serial/u64/sub.rs` pass.

At the end, commit your changes and print a short report of what you did

There's a 10% chance that the preconditions/postconditions of sub are wrong in some way that makes it unprovable---the correct thing to do in this case is change them to make sub provable, and loudly report that to me. But do not change them in a weaselly way

