"""Select matching modules whose entire local dependency closure also matches."""


def reusable_dependency_closure(candidates, dependencies):
    """Return the largest dependency-closed subset of hash-matching modules.

    An absent, changed, or cyclic dependency prevents reuse of its dependents.
    The result does not depend on the iteration order of the input mappings.
    """
    pending = set(candidates)
    reused = set()
    while pending:
        ready = {module for module in pending
                 if dependencies[module] <= reused}
        if not ready:
            break
        reused.update(ready)
        pending.difference_update(ready)
    return reused
