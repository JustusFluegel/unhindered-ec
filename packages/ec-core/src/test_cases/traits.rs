// TODO: @laundmo@twitch was concerned if this is overly generic and if we
// should just create 3 seperate methods, `fn into_iterator(self) -> impl
// Iterator<...>`` and the same thing for &self and &mut self instead
/// This trait represents a collection of test cases for the ec system
///
/// # How to implement
/// If you are implementing the [`CaseCollection`] trait for one of your own
/// types and not just using the provided implementations for Vec<T> you need to
/// make sure thet the following trait implementations are present as well:
///  - `impl IntoIterator for MyCollection`
///  - `impl<'a> IntoIterator for &'a MyCollection`
///  - `impl<'a> IntoIterator for &'a mut MyCollection`
pub trait CaseCollection<'a> {
    type Case: Case;

    fn count(&self) -> usize;

    fn get(&'a self, pos: usize) -> Option<&Self::Case>;
}

impl<'a, T> CaseCollection<'a> for &'a T
where
    T: CaseCollection<'a>,
{
    type Case = T::Case;

    fn count(&self) -> usize {
        (**self).count()
    }

    fn get(&self, pos: usize) -> Option<&Self::Case> {
        (**self).get(pos)
    }
}

pub trait Case {
    type Input;
    type Output;

    fn input(&self) -> &Self::Input;
    fn expected_output(&self) -> &Self::Output;
    fn check_matches(&self, output: &Self::Output) -> bool;
}

impl<Input, Output> Case for (Input, Output)
where
    Output: Eq,
{
    type Input = Input;

    type Output = Output;

    fn check_matches(&self, output: &Self::Output) -> bool {
        self.1.eq(output)
    }

    fn input(&self) -> &Self::Input {
        &self.0
    }

    fn expected_output(&self) -> &Self::Output {
        &self.1
    }
}

impl<'a, T> Case for &'a T
where
    T: Case,
{
    type Input = T::Input;

    type Output = T::Output;

    fn input(&self) -> &Self::Input {
        (**self).input()
    }

    fn check_matches(&self, output: &Self::Output) -> bool {
        (**self).check_matches(output)
    }

    fn expected_output(&self) -> &Self::Output {
        (**self).expected_output()
    }
}

impl<'a, T> Case for &'a mut T
where
    T: Case,
{
    type Input = T::Input;

    type Output = T::Output;

    fn input(&self) -> &Self::Input {
        (**self).input()
    }

    fn check_matches(&self, output: &Self::Output) -> bool {
        (**self).check_matches(output)
    }

    fn expected_output(&self) -> &Self::Output {
        (**self).expected_output()
    }
}

pub trait FromInputs<Input, Inputs, Output, F>
where
    Inputs: IntoIterator,
    F: Fn(&Inputs::Item) -> Output,
{
    fn from_inputs(inputs: Inputs, target_fn: F) -> Self;
}

pub trait WithTarget<Input, Output, Result> {
    type Iter<F>: Iterator<Item = Result>
    where
        F: Fn(&Input) -> Output;

    fn with_target<F>(self, target_fn: F) -> Self::Iter<F>
    where
        F: Fn(&Input) -> Output;
}
