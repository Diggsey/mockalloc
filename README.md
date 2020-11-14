# mockalloc

Mockalloc is a crate to allow testing code which uses the global allocator. It
uses a probabilistic algorithm to detect and distinguish several kinds of
allocation related bugs:

- Memory leaks
- Double frees
- Invalid frees (bad pointer)
- Invalid frees (bad size)
- Invalid frees (bad alignment)

## Usage

Typical use involves enabling the `Mockalloc` allocator during tests, eg:

```rust
#[cfg(test)]
mod tests {
    use std::alloc::System;
    use mockalloc::Mockalloc;

    #[global_allocator]
    static ALLOCATOR: Mockalloc<System> = Mockalloc(System);
}
```

Once the allocator is enabled, there are several ways to use it in your tests.

The easiest way is to use the `#[mockalloc::test]` attribute on your tests
instead of the usual `#[test]` attribute:

```rust
    #[mockalloc::test]
    fn it_works() {
        // Some code which uses the allocator
    }
```

The test will fail if any of the allocation bugs listed above are detected.
The test will also fail with the `NoData` error if no allocations are detected
so that you can be sure that the `Mockalloc` allocator is active.

You can also use `mockalloc` to test a specific section of code for memory
issues without checking the entire test using the `assert_allocs` function.

The `#[mockalloc::test]` attribute in the prior example is simply a shorthand
for:

```rust
    #[test]
    fn it_works() {
        mockalloc::assert_allocs(|| {
            // Some code which uses the allocator
        });
    }
```

It is also possible to make more detailed assertions: for example you may want
to assert that a piece of code performs a specific number of allocations. For
this you can use the `record_allocs` function:

```rust
    #[test]
    fn it_works() {
        let alloc_info = mockalloc::record_allocs(|| {
            // Some code which uses the allocator
        });

        assert_eq!(alloc_info.num_allocs(), 2);

        // This is what `assert_allocs` does internally:
        alloc_info.result().unwrap()
    }
```

## Limitations

Allocations are tracked separately for each thread. This allows tests to be
run in parallel, but it means that the library will report false positives
if a pointer returned by an allocation on one thread is later freed by a
different thread.

The algorithm cannot detect where the bug is, it can only indicate what
kind of bug is present.

## How it works

The allocator does its tracking without allocating any memory itself. It
uses a probabilistic algorithm which works by hashing various pieces of
metadata about allocations and frees, and then accumulating these using
a commutative operation so that the order does not affect the result.

Depending on which of these accumulators returns to zero by the end of
a region under test, different allocation bugs can be distinguished.

The following metadata is hashed and accumulated:

- Pointer
- Size & Pointer
- Alignment & Pointer

In addition to tracking the total number of allocations and frees.

We can detect memory leaks and double frees by looking for a difference
between the total numbers of allocations and frees.

Otherwise, if the pointer accumulator does not return to zero, we know that
an invalid pointer was freed.

Otherwise, we know the right pointers were freed, but maybe with the wrong
size and/or alignment, which we can detect with the other two accumulators.

If all accumulators returned to zero then we know everything is good.

Each accumulator and hash is 128 bits to essentially eliminate the chance
of a collision.
