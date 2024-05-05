use super::{Case, CaseCollection, FromInputs, WithTarget};

impl<'a, T> CaseCollection<'a> for Vec<T>
where
    T: Case + 'a,
{
    type Case = T;

    fn count(&self) -> usize {
        self.len()
    }

    fn get(&'a self, pos: usize) -> Option<&'a Self::Case> {
        (**self).get(pos)
    }
}

pub struct WithTargetsIter<I, F> {
    base: I,
    target_fn: F,
}

impl<I, F, Output> Iterator for WithTargetsIter<I, F>
where
    I: Iterator,
    F: Fn(&I::Item) -> Output,
{
    type Item = (I::Item, Output);

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.base.next()?;
        let output = (self.target_fn)(&next);

        Some((next, output))
    }
}

impl<T, Input, Output> WithTarget<Input, Output, (Input, Output)> for T
where
    T: IntoIterator<Item = Input>,
{
    type Iter<F> = WithTargetsIter<<T as IntoIterator>::IntoIter, F>
    where
        F: Fn(&Input) -> Output;

    fn with_target<F>(self, target_fn: F) -> Self::Iter<F>
    where
        F: Fn(&Input) -> Output,
    {
        WithTargetsIter {
            base: self.into_iter(),
            target_fn,
        }
    }
}

impl<Input, Inputs, Output, T, F> FromInputs<Input, Inputs, Output, F> for T
where
    Inputs: WithTarget<Input, Output, (Input, Output)> + IntoIterator<Item = Input>,
    F: Fn(&Input) -> Output,
    T: FromIterator<(Input, Output)>,
{
    fn from_inputs(inputs: Inputs, target_fn: F) -> Self {
        inputs.with_target(target_fn).collect()
    }
}

#[cfg(test)]
mod test {

    use crate::test_cases::{FromInputs, WithTarget};

    #[test]
    fn from_inputs_eq_with_target() {
        let test_cases = Vec::from_inputs([10i32, 100], |x| x.pow(2));

        let test_cases_2 = [10i32, 100].with_target(|x| x.pow(2)).collect::<Vec<_>>();

        assert_eq!(test_cases, test_cases_2);
    }

    #[test]
    fn select_random() {
        // let test_cases = [10i32, 100].with_target(|x|
        // x.pow(2)).collect::<Vec<_>>();

        // let selected_case = test_cases.select_random(&mut
        // thread_rng()).unwrap();

        // assert!(test_cases.contains(selected_case));
    }
}
