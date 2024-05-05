use crate::test_cases::CaseCollection;

pub struct CyclicFisherYates<'a, T: CaseCollection<'a>, Rng: rand::Rng> {
    cases: &'a T,
    shuffle: Vec<usize>,
    pivot: usize,
    direction: Direction,
    rng: &'a mut Rng,
}

#[derive(Clone, Copy)]
enum Direction {
    Right,
    Left,
}

impl Direction {
    fn switch(&mut self) {
        *self = match self {
            Direction::Right => Direction::Left,
            Direction::Left => Direction::Right,
        }
    }
}

// this has a memory complexity of O(|cases.count()|) but a time complexity for
// getting the next item of O(1)
impl<'a, U, Rng1> CyclicFisherYates<'a, U, Rng1>
where
    U: CaseCollection<'a>,
    Rng1: rand::Rng,
{
    pub fn new<'b, T, Rng>(cases: &'b T, rng: &'b mut Rng) -> CyclicFisherYates<'b, T, Rng>
    where
        T: CaseCollection<'b>,
        Rng: rand::Rng,
    {
        CyclicFisherYates {
            shuffle: (0..cases.count()).collect(),
            pivot: 0,
            cases,
            direction: Direction::Right,
            rng,
        }
    }
}

impl<'a, T, Rng> Iterator for CyclicFisherYates<'a, T, Rng>
where
    T: CaseCollection<'a> + 'a,
    Rng: rand::Rng,
{
    type Item = &'a T::Case;

    fn next(&mut self) -> Option<Self::Item> {
        if self.shuffle.len() == 0 {
            return None;
        }

        let range = match self.direction {
            Direction::Right => self.pivot..=(self.shuffle.len() - 1),
            Direction::Left => 0..=self.pivot,
        };

        let selected_pos = self.rng.gen_range(range);

        self.shuffle.swap(selected_pos, self.pivot);

        let choosen_index = self.shuffle[self.pivot];

        match (
            self.direction,
            self.pivot == self.shuffle.len() - 1,
            self.pivot == 0,
        ) {
            (Direction::Right, false, _) => self.pivot += 1,
            (Direction::Left, _, false) => {
                self.pivot -= 1;
            }
            _ => self.direction.switch(),
        }

        self.cases.get(choosen_index)
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashMap;

    use rand::{rngs::ThreadRng, thread_rng};

    use super::CyclicFisherYates;

    #[test]
    fn test_counting() {
        let expected_num = 1000;

        let test_cases = (0..1000).map(|x| (x, x)).collect::<Vec<_>>();

        let mut cases_count: HashMap<(i32, i32), usize> = HashMap::new();

        for case in
            CyclicFisherYates::<Vec<(i32, i32)>, ThreadRng>::new(&test_cases, &mut thread_rng())
                .cloned()
                .take(expected_num * test_cases.len())
        {
            *cases_count.entry(case).or_default() += 1
        }

        dbg!(&cases_count);
        assert!(cases_count.values().all(|&v| v == expected_num));
    }
}
