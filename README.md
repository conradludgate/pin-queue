# pin-queue

This crate provides `PinQueue`, a safe `Pin`-based intrusive linked list for a FIFO queue.

## Example

```rust
use std::sync::Arc;
use std::pin::Pin;

// define your node type (using pin-projection to project the intrusive node)
pin_project_lite::pin_project!(
    struct Node<V: ?Sized> {
        #[pin]
        intrusive: pin_queue::Intrusive<QueueTypes>,
        value: V,
    }
);

impl<V> Node<V> {
    pub fn new(value: V) -> Self {
        Self {
            intrusive: pin_queue::Intrusive::new(),
            value,
        }
    }
}

// Define how to acquire the intrusive values from the node
struct Key;
impl pin_queue::GetIntrusive<QueueTypes> for Key {
    fn get_intrusive(
        p: Pin<&Node<dyn std::fmt::Display>>
    ) -> Pin<&pin_queue::Intrusive<QueueTypes>> {
        p.project_ref().intrusive
    }
}

// alias of all the relevant types
type QueueTypes = dyn pin_queue::Types<
    // with checked IDs
    Id = pin_queue::id::Checked,
    // with this intrusive key
    Key = Key,
    // storing this pointer
    Pointer = Arc<Node<dyn std::fmt::Display>>
>;

let mut queue = pin_queue::PinQueue::<QueueTypes>::new(pin_queue::id::Checked::new());

// can push to the back
queue.push_back(Arc::pin(Node::new(1))).unwrap();
// can push many types
queue.push_back(Arc::pin(Node::new("hello"))).unwrap();

// can pop from the front
assert_eq!(queue.pop_front().unwrap().value.to_string(), "1");
assert_eq!(queue.pop_front().unwrap().value.to_string(), "hello");

assert!(queue.pop_front().is_none());
```

License: MIT
