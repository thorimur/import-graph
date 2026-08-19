
# Declarations in the module system

Given a declaration that uses another declaration, when will you get a module system error (like "invalid `public meta` definition"), and why? What are the rules for dependency the module system, and *why* are these the rules?

As we'll see, the module system's laws about declaration usage ultimately come from making sure that:

> *Core constraint*: **Everything code references is available when it needs to be**.

There are many possible "solutions" to that constraint (Lean itself pre-module system was one such solution!), but any such solution has three parts:

1. Reading/Loading: how data is made accessible (this may be constrained in certain ways)
2. Writing/Storing: where data gets stored (this may be specified in certain ways)
3. Cooperation: the laws data needs to satisfy due to how it's stored and will be accessed, and how its references are stored and accessed, so that Lean satisfies the core constraint.

Before the module system, the rules were simple:
1. Loading: load the data produced by every imported module, transitively.
2. Storing: store all the data produced by a module in a place associated with that module (the olean files).
3. Laws: you can only use imported declarations.

Note that while `private` declarations existed, they were still loaded, and you could write `open private foo ...` to get them. `private` was just an API-design affordance rather than part of the storing/loading story.

So why move to the module system? We get a lot of practical benefits from it: compilation speed improvements, smaller artifact size, and way less memory required. The guiding principle for achieving this (written down by someone else, likely Sebastian Ullrich, somewhere, but I can't recall where exactly) is "load less". Don't need it? Don't load it, and don't *provide* it to be loaded. Be deliberate about your "public API", the stuff that does get loaded by default, and hide the rest from downstream modules. And we need to be able to use the public API of other modules without ourselves asking downstream modules to load that too.

But, as you can see, this requires breaking loading chains (you can't just load everything transitively), which risks also breaking *reference* chains, and thus violating our core constraint. So we need to (or more preecisely, Sebastian Ullrich needed to) put some thought into how to achieve this.

To get more concrete, an import block, such as
```lean4
module

public meta import Bar
import Foo
```
is what you might call an *access specification* or a *load specification*. The important part for us is that Lean has rules for turning this surface-level specification into *loaded data* that may be accessed. Call those rules the **loading rules**.

Note that this may constrain the kinds of loaded configurations that may occur. For example, our rules may be such that you *cannot* express "load \[this data] without loading \[that data]", and thus \[this data] being loaded implies \[that data] being loaded. This implicit structure present in how things can get loaded will be used to our advantage to satisfy the core constraint!

So what are the loading rules? And what do we even need this data *for*?

Terminology: whether something is `public` or `private` is its *visibility*. Both import specifications and declarations can have visibility. We'll explain what each type of visibility means for each as we go.

Also, we'll start, in general, without considering the `meta` phase at all, and handle it in the next section.


It's easiest to treat the two visibilities as two different "scopes" for declarations in your file. Things (as we'll see, not just declarations!) in your module can be in the `public` scope or the `private` scope. (Note: this "scope" is not a single place in meta code, but a determination you can make at different places that store data. You can still think of each scope as a collection of data in your environment.)

The data in each of these scopes gets **stored** differently, in different `*.olean` files:

- public scope of `Foo` ↝ `Foo.olean`
- private scope of `Foo` ↝ `Foo.olean.private`

You can find these among the contents of your `.lake/build/lib/lean/*` folder, along with other artifacts!

(You'd also see `Foo.olean.server`, corresponding to the fact that the Lean language server needs to load *more stuff* to support interactivity, such as docstrings. We'll leave language server loading rule differences for later.)

Then the loading rules for a given import specification are:

- `A` has `public import B`: load the public data from `B` (stored in `B.olean`) into the *public scope* of the environment for `A`. Also load into the *public scope* of `A` all data that was loaded into the *public scope* of `B`.
- `A` has `import B`: load the public data from `B` (stored in `B.olean`) into the *private scope* of the environment for `A`. Also load into the *private scope* of `A` all data that was loaded into the *public scope* of `B`.
- `A` has `import all B`: do what `import B` does, but *also* load the private data from `B` (stored in `B.olean.private`) into the *private scope* of `A`. Also load into the *private scope* of `A` all data that was loaded into the *private scope* of `B`.

So for any visibility $v$ in {`public`, `private`}, any time we load the *output $v$ scope* of `B`, we also load the *input $v$ scope* of `B` (regardless of which scope $v'$ of `A` we put that scope into). And, whenever we load the `private` scope, we necessarily also load the `public` scope. Let's say that `public` is a "stricter" visibility than `private`.

We can visualize this with the following diagram:

[SCOPE FLOW TABLE]

What this means is that the following **cooperation law** is sufficient for visibility:

> New data in scope $v$ of `A` can only reference any data in a scope at least as strict as $v$.

For example, a `public` declaration's type can reference any `public` declaration, but cannot reference a `private` declaration, since the private scope is less strict than the public scope.

In fact, we can even go so far as to visualize the public scope being "contained within" the private scope. Note that if we wanted to, we could draw the following arrows *inside* each module depicting this, and composing all arrows transitively is in some sense "compatible" with the diagram from before!

[SCOPE FLOW TABLE + INTERNAL ARROWS]

I've been careful to say "new data", not "declarations".

This is partly because environment extensions can *also* choose the scope in which to put their data for olean storage (but the notion of separate "scopes" for env extension data *within a file* kind of falls apart for the most part).

But it's mostly because declarations have multiple pieces of data associated with them! Specifically, declarations generally have

1. a type signature
2. a body or "value"

You might imagine that the visibility of each of these pieces of data can be disentangled to some degree. This is where `@[expose]` comes in.

Actually, declarations usually have one more piece of data:

3. a name

Generally, you do not want a constant you can name but do not know the type of. So we say that if you have the name at some visibility, you also have the type at that visibility, too.

Moreover, you don't want to have a value at some visibility without also having its type! So we say that if you have the value at some visibility, you also have the type at a visibility **at least as strict** as the value's visibility.

So when a declaration and thus its type is `private`, we have no choice—the value must be `private` too. But we do have a choice when it's public, and this is what `@[expose]` controls. `@[expose]` upgrades a definition's value from `private` (the default) to `public` when the declaration is already `public`. In that case, if you have the declaration in some downstream scope (which, remember, could be private or public, depending on how this public declaration is imported), you'll also have its value in the same scope.

"Having the value" of a declaration actually means multiple things at once. It means for one that it's loaded (present in the environment, available to meta code), but it *also* means that you can *unfold* the `name` when it appears as a constant in an expression in certain circumstances (such as during definitional equality checks), as long as your unfolding is happening at or above the declaration's intrinsic *transparency*. Transparency is otherwise independent of visibility, but it's important to note that upgrading the visibility of the body to public via `@[expose]` generally comes along with enabling this rewrite from `foo` to its value. In some sense, you're not just making the value public when you attach `@[expose]`, you're making the rewrite rule public.

Theorems, it must be said, are disallowed from participating in this system. Their values are *always* private, and attaching `@[expose]` to a theorem will earn you a warning squiggle. This does us no harm on the type theory level due to proof irrelevance.

Note: `opaque` definitions are called opaque because their values are *never* available to the type theory, no matter what. This is stronger than a definition with a private body, which can be unfolded when the private scope is available (such as in the same module). However, they do still have some value that's inspectable at the meta level, since (1) they are meant only to enable conservative extensions to your type theory (essentially acting like global free variables), and are not axioms, so you must prove you have *some* term of that type prove you're not breaking the type theory by making the opaque definition in the first place (2) they must be represented as *something* when they are compiled to code and then executed (i.e. "at runtime").

So that's basically it. Data is split into two visibility scopes, and stored in two separate artifacts. Loading lets us put the output scope of a given module into a scope that is not more strict than the originating scope (you can't lift the private scope to the public scope, only downgrade public to private), and scopes are followed transitively. Data can only reference data from scopes at least as strict as its visibility (private can reference public but not the other way around).

Put these facts together, and you find that any reference which was allowed to have been created in the first place only exposes references which must be loaded along with it. We've satisfied the core constraint!

## The `meta` phase

This is where things start to get more involved.

### Lean IR

We need now to reckon with what meta code actually *is*. We avoided talking about code and execution in the previous section, thinking entirely type-theoretically. But the core constraint takes on a much more concrete meaning here.

Every (computable) Lean definition is compiled to "Lean IR", where "IR" stands for "intermediate representation". It's "intermediate" between Lean expressions (the substance of the type theoretical terms that we were talking about last section, e.g. the types and values of declarations) and C code. There are therefore two "compilers": one from Lean declarations (with expression content) to Lean IR, and one from Lean IR to C.

The IR Lean produces can be shown with `set_option trace.Compiler.result`. For example:

```lean4
set_option trace.Compiler.result true

/--
trace: [Compiler.result] size: 2
    def foo @&n : tobj :=
      let _x.1 := 2;
      let _x.2 := Nat.mul _x.1 n;
      return _x.2
[Compiler.result] size: 2
    def foo._boxed n : tobj :=
      let res := foo n;
      dec n;
      return res
-/
#guard_msgs in
public def foo (n : Nat) : Nat := 2 * n
```

(Note: the `def` in the compiled code shouldn't be confused with the `def` of surface-level Lean; these are IR `def`s we're seeing.)

You'll notice that this code is very simple and imperative, structurally. In fact, it's so simple that it can be *executed* one step at a time by some other program. That other program is called the *interpreter*, and this process of executing IR step-by-step is accordingly called *interpretation*.

Note the difference between this and *compilation*. Compilation transforms all the code into C code, then transforms all of *that* code using a C compiler into (eventually) machine code, whose bits your device is hardwired to be able to execute by how its circuitry is laid out. Interpretation gets a separate program (the Lean interpreter) to look at the IR and do the action corresponding to the what the IR says, skipping compilation. The interpreter has itself been compiled and knows on a "circuitry level" how to turn each Lean IR command into real computations, but the IR you're feeding in can be anything.

In particular, the IR can, in principle...be wrong. Above, the IR includes the constant `Nat.mul`. But more properly, the IR doesn't contain the constant; it contains the *name* "`Nat.mul`" The interpreter, upon seeing that name, looks up the code associated with that "`Nat.mul`" and executes it.

As such, the code associated with that name had better be available to the interpreter! So, either it's "built in" and the interpreter has `Nat.mul` available wherever it goes, or we've *loaded* the IR for `Nat.mul` (along with the dictionary saying that this code is the code named "`Nat.mul`").

If we haven't, the interpreter gives up and spits out an error like:
```
(interpreter) unknown declaration 'foo'
```
or, if it knows about the declaration but fails when trying to look up the IR:
```
(interpreter) IR of declaration 'foo' not available; this may point to a missing `meta` check in a metaprogram
```
This is quite rare, as this is exactly what the module system is designed to prevent! Getting to this point means having violated the core constraint. (But as the second one hints at, we'll see that it's not perfect, and there is still one kind of situation where a metaprogrammer must take on the responsibility of preserving the core constraint.)

### Flow of IR

So where do the interpreter and IR fit into the meta phase?

The meta phase governs IR which can be **executed during elaboration** by the interpreter.

So, for example, when Lean applies a macro or elaborator to syntax you write, or runs a tactic, that's the interpreter executing the IR associated with that computation.

This IR Lean is running (and any IR it references!) must be *loaded* for the interpreter to execute it, and whether it's loaded or not is as usual determined by the loading rules applied to the import specification. We'll describe those loading rules shortly, but first, where does that IR come from? I.e., where *is* the IR which we want to load actually stored on disk?

There are two places:

1. The `*.olean`(s)
2. The `*.ir` files

`meta def`s get compiled into IR which is stored in the `*.olean`s *and* the `*.ir` files, whereas non-`meta` `def`s get compiled into IR that's stored (only) in the `*.ir` files.

So, to be clear, both `meta` and non-`meta` declarations are eventually compiled to IR. The difference (well, one difference) is where that IR is stored.

To get ahead of it, a trick the loading rules are going to use here is that we have the can load code for elaboration-time execution from the `*.ir` files *without* also loading the `*.olean`s. Loading the `*.olean`s would pollute our type-theory environment and make "loading" much more intensive. Remember, we want to load less!

(This separation is part of what earns the notion that "elaboration-time" code is really a separate "phase" from "static code", and this theme of separation will continue to show up. Note: in Lean core you'll see the IR phases denoted as "compile time" and "runtime", but I find this terminology confusing pedagogically.)

Now let's turn to actually loading these artifacts.

The first thing to observe is that a `(public) meta import` actually must fulfill two distinct functions:

1. **Execution**: provide access to IR that may be executed while elaborating the current file
2. **Code reference**: allow (meta) code written in the current file to refer to and use upstream constants

Now, by applying the core constraint to these situations, we realize both of these must come with certain promises about how they work in order to fulfill it.

1. **Execution promise**: make sure that any IR which may be executed in the current file is reference-closed
2. **Code reference promise**: make sure that any IR *produced* by the current module which may be run downstream will necessarily have its references loaded for execution whenever this newly-produced IR is loaded for execution 

Let's first think about 

---

NOTES (in progress)

The meta closure is duplicated from oleans into IR. The rest of the IR is exactly stuff that didn't make it into the meta closure.

So, interestingly, meta code becomes *unavailable* (for execution during elaboration) under the same circumstances downstream, but for different reasons. For example, if I make it a public meta def, and then regular-import that module, then regular-import *that* module, the module with the meta def is not data-reachable, and so we can't run its IR from its olean. If instead I make it a public def and change the first import to a meta import to get the IR, we never hit needsIRTrans and therefore never load the module's IR.


The question is:

For each loaded thing under each certain circumstance, where can the necessary references it demands live relative to it? And then, given that circumstance, what else is loaded?

And on the production side, where will this data end up (function of data spec + module state)? When it is loaded under each circumstance, what references must be completable? What must therefore be denied during production as invalid?


Should probably show the example with the private meta def being swept up into the meta closure by a public meta def which induces a (new) public meta check on the private meta defs value.


Why does shake record a meta usage when really it's an IR usage? Answer: for syntax and such, it's actually a meta usage. ...Well, for parsing. I'm actually still on the fence about initialized attributes. That's an SQ: why do initializers travel through IR?




