use crate::{KaniIntoIter, KaniSingleIter};

impl<T: Copy> KaniIntoIter for Vec<T> {
    type Iter = KaniSingleIter<T>;
    fn kani_into_iter(self) -> Self::Iter {
        let s = self.iter();
        KaniSingleIter::new(s.as_slice().as_ptr(), s.len())
    }
}
