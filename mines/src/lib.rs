/// A minesweeper solver.

pub mod solver {
    use std::collections::{HashMap, HashSet, VecDeque};
    use std::hash::Hash;
    use std::rc::Rc;

    #[derive(PartialEq, Eq)]
    pub struct Information<S: Hash + Eq + Copy> {
        spaces: Rc<HashSet<S>>,
        count: i32,
    }

    /// The `SolverResult` type.
    /// Characterizes the solver's current knowledge about the number of solutions.
    enum SolveResult {
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
        spaces: HashSet<S>,
        solved_spaces: HashMap<S, bool>,
        informations_for_space: HashMap<S, Vec<Information<S>>>,
        spaces_to_add: VecDeque<S>,
        informations_to_add: VecDeque<Information<S>>,
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
        pub fn new(spaces: HashSet<S>) -> Solver<S> {
            Solver::<S> {
                spaces: spaces,
                solved_spaces: HashMap::<S, bool>::new(),
                informations_for_space: HashMap::<S, Vec<Information<S>>>::new(),
                spaces_to_add: VecDeque::<S>::new(),
                informations_to_add: VecDeque::<Information<S>>::new(),
            }
        }
    }
}

#[cfg(test)]
mod test {
    #[test]
    fn it_works() {
        
    }
}
