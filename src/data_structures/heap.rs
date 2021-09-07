/// Implementation of a heap / priority queue
///
/// Heaps are vectors where `a[k] <= a[2*k+1]` and `a[k] <= a[2*k+2]` for
/// all k, counting elements from 0.  For the sake of comparison,
/// non-existing elements are considered to be infinite.  The interesting
/// property of a heap is that a\[0\] is always its smallest element.
///
/// Our API differs from textbook heap algorithms as follows:
/// - We use 0-based indexing.  This makes the relationship between the
///   index for a node and the indexes for its children slightly less
///   obvious, but is more suitable since Rust uses 0-based indexing.
/// - The [Heap::pop] method returns the smallest item, not the largest.
///
/// Note: This explanation is taken from CPython's Heapq implementation

#[derive(Clone, Default, Debug)]
pub struct Heap<T> {
    data: Vec<T>,
}

impl<T> Heap<T> {
    pub fn new() -> Self {
        Heap { data: Vec::new() }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Heap {
            data: Vec::with_capacity(capacity),
        }
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    pub fn capacity(&self) -> usize {
        self.data.capacity()
    }

    pub fn into_vec(self) -> Vec<T> {
        self.data
    }
}

impl<T: Ord> Heap<T> {
    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            let i = self.len() - 1;
            self.data.as_mut_slice().swap(0, i);
            let result = self.data.remove(i);
            self.sift_down(0);
            Some(result)
        }
    }

    pub fn push(&mut self, value: T) {
        self.data.push(value);
        let i = self.len() - 1;
        self.sift_up(i);
    }

    /// Heap allocation free: faster than `vec.into_iter().collect()`
    pub fn from_vec(vec: Vec<T>) -> Self {
        let range = 0..vec.len();
        let mut heap = Heap { data: vec };
        for index in range {
            heap.sift_up(index)
        }
        heap
    }

    fn sift_up(&mut self, child: usize) {
        if let Some(parent) = Self::parent_index(child) {
            if self.data.get(child) < self.data.get(parent) {
                self.data.as_mut_slice().swap(child, parent);
                self.sift_up(parent);
            }
        }
    }

    fn sift_down(&mut self, parent: usize) {
        let l = Self::left_child_index(parent);
        let r = Self::right_child_index(parent);

        let child = match (l < self.len(), r < self.len()) {
            // Both children exist, select smaller element
            (true, true) => std::cmp::min_by_key(l, r, |&i| self.data.get(i)),
            // Only left child exists
            (true, false) => l,
            // Only right child exists
            (false, true) => unreachable!("Left child must exist if right child exists"),
            // No children (base case)
            (false, false) => return,
        };

        if self.data.get(child) < self.data.get(parent) {
            self.data.as_mut_slice().swap(child, parent);
            self.sift_down(child);
        }
    }

    /// Returns the index of the given index's parent or `None`
    fn parent_index(i: usize) -> Option<usize> {
        if i == 0 {
            None
        } else {
            Some((i - 1) / 2)
        }
    }

    /// Returns the index of the given index's left child.
    /// Index may be larger than the current capacity of the heap.
    /// Always smaller than right index
    fn left_child_index(i: usize) -> usize {
        (i + 1) * 2 - 1
    }

    /// Returns the index of the given index's right child.
    /// Index may be larger than the current capacity of the heap.
    /// Always larger than left index
    fn right_child_index(i: usize) -> usize {
        (i + 1) * 2
    }
}

impl<T: Clone> Heap<T> {
    /// Return a clone of the top item in the heap
    pub fn peek(&self) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            Some(self.data[0].clone())
        }
    }
}

use std::iter::Iterator;
impl<T: Ord> Iterator for Heap<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.pop()
    }
}

use std::iter::FromIterator;
/// Enables `.collect::<Heap<_>>()`
impl<T: Ord> FromIterator<T> for Heap<T> {
    fn from_iter<I: IntoIterator<Item = T>>(into_iter: I) -> Self {
        let iter = into_iter.into_iter();
        let (cap, _) = iter.size_hint();
        let mut heap = Heap::with_capacity(cap);
        for i in iter {
            heap.push(i);
        }
        heap
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_collect() {
        let _heap = vec![7, 8, 9].iter().collect::<Heap<_>>();
    }

    #[test]
    fn test_peek() {
        let mut heap = Heap::new();
        heap.push(1);
        assert_eq!(heap.peek(), Some(1));
        assert_eq!(heap.peek(), Some(1));
        assert_eq!(heap.pop(), Some(1));
    }

    #[test]
    fn test_empty_heap() {
        let mut heap = Heap::new();
        heap.push(1);
        assert_eq!(heap.pop(), Some(1));
        assert_eq!(heap.pop(), None);
    }

    #[test]
    fn test_min_heap() {
        let mut heap = Heap::new();
        heap.push(4);
        heap.push(2);
        heap.push(9);
        heap.push(11);
        assert_eq!(heap.len(), 4);
        assert_eq!(heap.pop(), Some(2));
        assert_eq!(heap.pop(), Some(4));
        assert_eq!(heap.pop(), Some(9));
        heap.push(1);
        assert_eq!(heap.pop(), Some(1));
    }

    #[test]
    fn test_max_heap() {
        use std::cmp::Reverse;
        let mut heap = Heap::new();
        heap.push(Reverse(4));
        heap.push(Reverse(2));
        heap.push(Reverse(9));
        heap.push(Reverse(11));
        assert_eq!(heap.len(), 4);
        assert_eq!(heap.pop(), Some(Reverse(11)));
        assert_eq!(heap.pop(), Some(Reverse(9)));
        assert_eq!(heap.pop(), Some(Reverse(4)));
        heap.push(Reverse(1));
        assert_eq!(heap.pop(), Some(Reverse(2)));
    }

    fn is_sorted<T: Ord>(data: &[T]) -> bool {
        data.windows(2).all(|w| w[0] <= w[1])
    }

    #[test]
    fn test_big() {
        let vals = vec![
            47, 44, 9, 31, 7, 19, 24, 63, 25, 0, 19, 23, 54, 27, 1, 98, 19, 81, 65, 31, 41, 30, 4,
            65, 28, 62, 15, 98, 60, 28, 79, 93, 42, 68, 78, 64, 60, 61, 25, 16, 42, 92, 9, 5, 59,
            43, 17, 23, 54, 11, 37, 35, 56, 9, 69, 57, 68, 41, 15, 84, 35, 86, 20, 12, 73, 44, 96,
            68, 79, 94, 77, 15, 12, 48, 65, 58, 87, 21, 48, 78, 37, 90, 49, 70, 21, 96, 58, 58, 87,
            94, 97, 27, 89, 92, 39, 81, 38, 62, 37, 67, 22, 23, 88, 40, 24, 30, 93, 47, 79, 0, 91,
            89, 6, 17, 70, 96, 5, 2, 74, 87, 78, 75, 79, 88, 73, 32, 20, 15, 7, 47, 55, 80, 72, 87,
            29, 20, 8, 76, 41, 68, 2, 46, 11, 18, 57, 84, 10, 61, 89, 15, 57, 24, 26, 94, 20, 82,
            66, 73, 66, 62, 34, 44, 62, 98, 31, 88, 41, 58, 65, 91, 44, 24, 97, 10, 17, 87, 74, 21,
            71, 97, 16, 6, 21, 96, 90, 96, 6, 97, 64, 21, 12, 93, 20, 13, 19, 56, 27, 44, 41, 41,
            95, 76, 38, 6, 23, 18, 12, 89, 28, 79, 62, 95, 95, 63, 78, 98, 72, 87, 51, 50, 12, 5,
            12, 87, 70, 60, 89, 59, 70, 1, 37, 38, 90, 64, 93, 89, 84, 2, 17, 22, 59, 73, 49, 61,
            70, 65, 74, 75, 93, 91, 67, 2, 75, 32, 96, 2, 24, 97, 0, 20, 87, 91, 66, 39, 44, 26, 2,
            6, 90, 55, 11, 34, 82, 22, 60, 29, 80, 61, 32, 20, 65, 34, 38, 44, 56, 73, 33, 44, 33,
            13, 97, 26, 42, 19, 37, 75, 62, 74, 9, 70,
        ];
        let heap = vals.iter().collect::<Heap<_>>();
        assert!(
            is_sorted(&heap.collect::<Vec<_>>()),
            "Could not sort {:?}",
            vals
        )
    }

    #[test]
    fn test_from_vec() {
        let vals = vec![6, 90, 55, 11, 34, 82, 22, 60, 29, 80, 61, 32, 20];
        let heap = Heap::from_vec(vals.clone());
        assert!(
            is_sorted(&heap.collect::<Vec<_>>()),
            "Could not sort {:?}",
            vals
        )
    }
}
