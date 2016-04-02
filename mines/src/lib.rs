/// A minesweeper solver.

pub mod solver {
    use std::convert::AsRef;
    use std::collections::{HashMap, HashSet, VecDeque};
    use std::iter::FromIterator;
    use std::hash::Hash;
    use std::rc::Rc;

    #[derive(PartialEq, Eq, Clone)]
    pub struct Information<S: Hash + Eq + Copy> {
        spaces: Rc<HashSet<S>>,
        count: i32,
    }

    impl<S: Hash + Eq + Copy> Information<S> {
        pub fn new<T>(count:i32, spaces:T) -> Information<S> where Rc<HashSet<S>>: From<T> {
            Information::<S> {
                count: count,
                spaces: Rc::<HashSet<S>>::from(spaces),
            }
        }

        pub fn from_iter<T>(count:i32, spaces: T) -> Information<S> where T: IntoIterator<Item=S> {
            Information::<S>::new(count, Rc::from(HashSet::<S>::from_iter(spaces)))
        }
    }

    /// The `SolveResult` type.
    /// Characterizes the solver's current knowledge about the number of solutions.
    #[derive(PartialEq, Eq, Debug)]
    pub enum SolveResult {
        /// There are no possible solutions / information supplied was inconsistent.
        NoSolution,
        /// There is exactly one solution.
        OneSolution,
        /// There is more than one solution.
        MultipleSolutions,
        /// The solver has not done enough work to determine the number of solutions.
        Unknown,
    }

    /// The `Solver` type. Represents everything known in a specific minesweeper game.
    ///
    /// The S type represents a space on the board, which may be a "mine" or a "clear space".
    /// The type must have the Hash, Eq, and Copy traits.
    ///
    /// Typically S will be a tuple x and y coordinates, like (i32, i32), but
    /// the type is left unspecified to allow for alternative geometries.
    pub struct Solver<S: Hash + Eq + Copy> {
        spaces: Rc<HashSet<S>>,
        solved_spaces: HashMap<S, bool>,
        informations_for_space: HashMap<S, Vec<Information<S>>>,
        spaces_to_add: VecDeque<S>,
        informations_to_add: VecDeque<Information<S>>,
        solve_result: SolveResult,
    }

    impl<S: Hash + Eq + Copy> Solver<S> {
        /// Constructs a new Solver.
        ///
        /// # Examples
        /// ```
        /// use mines::solver::Solver;
        /// use std::collections::HashSet;
        /// use std::iter::FromIterator;
        /// 
        /// let spaces = HashSet::<i32>::from_iter(0..10);
        /// let solver = Solver::<i32>::new(spaces);
        /// ```
        pub fn new<T>(spaces: T) -> Solver<S> where Rc<HashSet<S>>: From<T> {
            Solver::<S> {
                spaces: Rc::<HashSet<S>>::from(spaces),
                solved_spaces: HashMap::<S, bool>::new(),
                informations_for_space: HashMap::<S, Vec<Information<S>>>::new(),
                spaces_to_add: VecDeque::<S>::new(),
                informations_to_add: VecDeque::<Information<S>>::new(),
                solve_result: SolveResult::Unknown,
            }
        }

        pub fn from_iter<T>(spaces: T) -> Solver<S> where T: IntoIterator<Item=S> {
            Solver::<S>::new(Rc::from(HashSet::<S>::from_iter(spaces)))
        }

        /// Add information to a Solver.
        ///
        /// In most cases, this just queues up work to be done by solve() later.
        ///
        /// # Examples
        /// ```
        /// use mines::solver::{Solver, Information};
        /// 
        /// let mut solver = Solver::<i32>::from_iter(0..10);
        ///
        /// // 5 mines total in all spaces
        /// let information = Information::<i32>::from_iter(5, (0..10));
        /// solver.add_information(information);
        ///
        /// // 3 mines total in the first 5 spaces
        /// let information = Information::<i32>::from_iter(3, (0..5));
        /// solver.add_information(information);
        /// ```
        pub fn add_information(&mut self, information: Information<S>) -> SolveResult {
            if self.solve_result == SolveResult::NoSolution {
                return SolveResult::NoSolution;
            }

            if information.count < 0 {
                self.solve_result = SolveResult::NoSolution;
                return SolveResult::NoSolution;
            }

            {
                let spaces = information.spaces.as_ref();
                let len = spaces.len() as i32;

                if information.count > len {
                    self.solve_result = SolveResult::NoSolution;
                    return SolveResult::NoSolution;
                }

                // FIXME: Add known spaces if count is 0 or len
            }

            self.informations_to_add.push_back(information);
            SolveResult::Unknown
        }
    }
}

#[cfg(test)]
mod test {
    use super::solver::{Solver, SolveResult, Information};
    use std::collections::HashSet;
    use std::iter::FromIterator;

    #[test]
    fn bad_information_count() {
        let mut solver = Solver::<i32>::from_iter(0..10);

        let valid_information = Information::from_iter(1, (0..10));
        let valid_res = solver.add_information(valid_information.clone());
        assert!(valid_res == SolveResult::MultipleSolutions || valid_res == SolveResult::Unknown);

        let bad_information = Information::from_iter(-1, (0..10));
        assert_eq!(SolveResult::NoSolution, solver.add_information(bad_information));

        assert_eq!(SolveResult::NoSolution, solver.add_information(valid_information.clone()));

        let mut solver = Solver::<i32>::from_iter(0..10);

        let bad_information = Information::from_iter(12, (0..10));
        assert_eq!(SolveResult::NoSolution, solver.add_information(bad_information));

        assert_eq!(SolveResult::NoSolution, solver.add_information(valid_information.clone()));
    }
}
