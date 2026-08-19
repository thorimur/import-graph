# Modeling influence traceably

Declarations are more than just declarations, but they're a great example of how demands and provisions interact.

In general, here is the situation we are looking at. There is some event D. It depends on some persistent effects I in various manners M(i) and has some persistent effects O.

Let's think about the case where D is a declaration command (hence the letter).

For simplicity's sake, let's say we have certain *enforcers* that enforce various properties are true about the (effects of the) event D and/or the way the input effects are accessed/provisioned. All we care about (for now) is the success or failure of creating the (1) the original effect(s) (2) without errors from any enforcers. (In general we might instead have data at play here: measurements of the effects, the effects themselves, etc. But this is complicated enough.)

In our case we don't have control over the "access manner" of input effects, but hypothetically we might (if we were considering altering the declaration's visibility, for instance). There simply "are" different access manners occurring in our declaration command (e.g. "constant reference in the type", "constant reference in the value"). This includes in it the notion of "position", "where" in the command we access from, which covers basically all of our cases. We'll use the terms "access manner" and "position" more or less interchangeably. We want to assign to each position a "demand", a reification/tokenization/serialization of the "state of availability" the object in question must satisfy at that position. (The type of this state may depend on the object whose type may in turn depend on the position.)

We *do* have control over the way the input effects are provisioned: in our case, the imports. We won't split this further into "whether provisioned" and "how provisioned (e.g. the import modifiers)". Instead, we'll regard it as a property our provisioning state must satisfy. We then later "solve for the provision state" which satisfies this property (there may be multiple). This allows us to easily compose properties just through "and", e.g. "Foo must be imported at least public visibility, any phase" & "Foo must be imported in the meta phase".

The insight here is that "behavior of enforcers" as a function from effects (and inputs???) -> Bool corresponds to data used to characterize "demands", which in turn correspond to provisioning properties.

When enforcers act "at a location", we can think of a demand as being attached to that position, as well. Variation in how enforcers treat positions in some sense *define* positions?

Moreover, the way that we can *change* provisioning, or the space of possibilities for provisioning, and how this might affect enforcer behavior, determines the space of demands. For example, we might import publicly or not. This difference might change how enforcers behave.

As an example, what if our effect was a natural number, and we had one enforcer which returned true if even and false if not? And we could either provision our natural number as is, or we could divide by two? Our classes become "double of an odd number", "odd", and "other even number". And so our space of reified demands has three tokens in it.

---

Let's dive into the declaration example more specifically.

## Manners of provisioning

- IR: A declaration's IR "phase" can either be
  - Available at `.comptime`: during elaboration, Lean can actually look up the IR associated with a constant (say, an elaborator) and interpret it to effect elaboration.
  - Available for `.runtime`: Lean

## Enforcers

- `checkMeta`: This inspects the IR effect. A declaration (optionally) produces IR that is ready for interpretation and compilation to C. This is post-inlining

