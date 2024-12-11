#![allow(dead_code, unused_variables)]

//! # Wordle Game Module
//!
//! This module implements the core logic for a simplified version of the Wordle game.
//! It includes structures, traits, and utilities to define the game's mechanics, such as
//! handling guesses, validating words, and calculating correctness feedback.
//!
//! ## Overview
//!
//! The Wordle game challenges players to guess a hidden word within a limited number of attempts.
//! Each guess receives feedback indicating how accurate it is:
//! - **Correct**: A letter is in the correct position.
//! - **Misplaced**: A letter is in the word but in the wrong position.
//! - **Incorrect**: A letter is not in the word.
//!
//! ## Main Components
//!
//! - [`Wordle`]: The primary struct that manages the game state, including the dictionary of valid words.
//! - [`Guess`]: Represents a single guess made during the game.
//! - [`Guesser`]: A trait for implementing different guessing strategies.
//! - [`Correctness`]: An enum defining the feedback for guessed letters.
//!
//! ## Example Usage
//!
//! ```rust
//! use wordle::game::{Wordle, Guesser, Guess};
//!
//! struct SimpleGuesser;
//! impl Guesser for SimpleGuesser {
//!     fn guess(&mut self, _previous: &[Guess]) -> String {
//!         "apple".to_string()
//!     }
//! }
//!
//! let game = Wordle::new();
//! let result = game.play("apple", SimpleGuesser);
//! assert_eq!(result, Some(1)); // Guessed correctly in 1 attempt
//! ```
//!
//! ## Features
//!
//! - **Dictionary Management**: The game loads a dictionary of valid words at compile time.
//! - **Custom Guessing Strategies**: Users can implement the [`Guesser`] trait to create their own guessing logic.
//! - **Flexible Feedback**: The [`Correctness`] enum provides detailed feedback on each guess.
//!

use std::collections::HashSet;

/// The dictionary of valid words for the Wordle game.
///
/// This constant is a static string that includes all valid words separated by whitespace.
/// It is loaded at compile time using the `include_str!` macro, ensuring that the dictionary
/// is embedded directly into the compiled binary.
///
/// # File Format
/// - The file should contain words separated by whitespace (e.g., spaces, newlines, or tabs).
/// - The format is the following:
/// ```txt
/// word1 9999
/// word2 1111
/// ... and so on
/// ```
///
/// While the number is the number of times the word appears in Google's books, it is not used for this part of the game.
///
/// # Source
/// The dictionary is sourced from `dictionary.txt`, located at root directory of the project.
///
const DICTIONARY: &str = include_str!("../dictionary.txt");

/// Represents the Wordle game, including its dictionary of valid words.
///
/// The `Wordle` struct manages the dictionary, ensuring that only valid words can be guessed
/// or used as answers. The dictionary is built at runtime from the static `DICTIONARY` constant.
///
/// # Fields
/// - `dictionary`: A private `HashSet` containing valid words, derived from the `DICTIONARY` constant.
///
pub struct Wordle {
    dictionary: HashSet<&'static str>,
}

impl Wordle {
    /// Creates a new instance of the Wordle game, initializing the dictionary of valid words.
    ///
    /// This constructor processes the static `DICTIONARY` constant, splitting it by whitespace and
    /// including only every second word in the resulting `HashSet`. This design allows for selective
    /// filtering of the dictionary contents.
    ///
    /// # Returns
    /// A `Wordle` instance with a populated dictionary.
    ///
    /// # Behavior
    /// - The dictionary is created at runtime by iterating over the words in the static `DICTIONARY`.
    /// - Words are filtered to include only every second entry using `step_by(2)`.
    ///
    /// # Example
    /// ```
    /// use wordle::game::Wordle;
    ///
    /// let game = Wordle::new();
    /// ```
    pub fn new() -> Self {
        Self {
            dictionary: HashSet::from_iter(DICTIONARY.split_whitespace().step_by(2)),
        }
    }

    /// Simulates a game of Wordle, allowing a `Guesser` to play against a given answer.
    ///
    /// This method orchestrates the Wordle game logic by iteratively asking the provided `Guesser`
    /// to make guesses based on the feedback from previous guesses. It checks the correctness of
    /// each guess and stops the game if the correct answer is guessed or the maximum number of
    /// attempts (32) is reached.
    ///
    /// # Parameters
    /// - `answer`: The correct word to be guessed. This must be a valid static string in the dictionary.
    /// - `guesser`: An implementation of the `Guesser` trait, responsible for generating guesses based on feedback.
    ///
    /// # Returns
    /// - `Some(usize)`: The number of guesses taken to correctly guess the answer, if successful.
    /// - `None`: If the `Guesser` fails to find the correct answer within 32 attempts.
    ///
    /// # Behavior
    /// - Each guess is validated to ensure it exists in the provided dictionary.
    /// - The correctness of each guess is computed using [`Correctness::compute`].
    /// - Previous guesses and their feedback are stored and passed back to the `Guesser` for the next round.
    ///
    /// # Example
    /// ```
    /// use wordle::game::{Wordle, Guesser, Guess};
    ///
    /// struct SimpleGuesser;
    /// impl Guesser for SimpleGuesser {
    ///     fn guess(&mut self, _previous: &[Guess]) -> String {
    ///         "apple".to_string()
    ///     }
    /// }
    ///
    /// let game = Wordle::new();
    /// let result = game.play("apple", SimpleGuesser);
    ///
    /// assert_eq!(result, Some(1)); // The guesser found the answer in 1 attempt.
    /// ```
    ///
    /// # Panics
    /// - Panics if a guess made by the `Guesser` is not found in the dictionary.
    ///
    /// # Limitations
    /// - The method assumes that `answer` is a valid word present in the dictionary.
    ///   Providing an invalid answer will result in undefined behavior.
    pub fn play<G: Guesser>(&self, answer: &'static str, mut guesser: G) -> Option<usize> {
        let mut previous = Vec::new();
        for i in 1..=32 {
            let guess = guesser.guess(&previous);
            if guess == answer {
                return Some(i);
            }

            assert!(self.dictionary.contains(&*guess));

            let correctness = Correctness::compute(answer, &guess);
            previous.push(Guess {
                word: guess,
                correctness,
            });
        }

        None
    }
}

/// Provides a default implementation for the `Wordle` game.
///
/// This implementation simply delegates to the [`Wordle::new`] method, allowing the use of
/// the `Default` trait to create a new game instance.
///
/// # Example
/// ```
/// use wordle::game::Wordle;
///
/// let game = Wordle::default(); // Equivalent to Wordle::new()
/// ```
impl Default for Wordle {
    fn default() -> Self {
        Self::new()
    }
}

/// Represents a single guess made in the Wordle game.
///
/// Each guess consists of the guessed word and the correctness feedback for each character.
/// The correctness feedback is represented as an array of [`Correctness`] values.
///
/// # Fields
/// - `word`: The guessed word as a `String`.
/// - `correctness`: An array of [`Correctness`] values representing the feedback for each character.
///
/// # Example
/// ```
/// use wordle::game::{Guess, Correctness};
///
/// let guess = Guess {
///     word: "apple".to_string(),
///     correctness: [
///         Correctness::Correct,
///         Correctness::Misplaced,
///         Correctness::Incorrect,
///         Correctness::Correct,
///         Correctness::Incorrect,
///     ],
/// };
/// ```
pub struct Guess {
    pub word: String,
    pub correctness: [Correctness; 5],
}

/// A trait for implementing guessing strategies in the Wordle game.
///
/// The `Guesser` trait defines a single method, [`guess`], which generates a guess based on the
/// history of previous guesses and their correctness feedback.
///
/// # Required Methods
/// - `guess`: Produces a new guess based on the feedback from previous guesses.
///
/// # Example
/// ```
/// use wordle::game::{Guesser, Guess, Correctness};
///
/// struct SimpleGuesser;
/// impl Guesser for SimpleGuesser {
///     fn guess(&mut self, _previous: &[Guess]) -> String {
///         "apple".to_string()
///     }
/// }
///
/// let mut guesser = SimpleGuesser;
/// let guess = guesser.guess(&[]);
/// assert_eq!(guess, "apple");
/// ```
pub trait Guesser {
    /// Generates a new guess based on the history of previous guesses.
    ///
    /// This method is called each turn to produce a guess. It receives the list of previous
    /// guesses and their corresponding correctness feedback, allowing the implementation
    /// to refine its strategy based on past results.
    ///
    /// # Parameters
    /// - `previous`: A slice of [`Guess`] containing all previous guesses and their feedback.
    ///
    /// # Returns
    /// A `String` representing the next guessed word.
    ///
    /// # Example
    /// ```
    /// use wordle::game::{Guesser, Guess, Correctness};
    ///
    /// struct SimpleGuesser;
    /// impl Guesser for SimpleGuesser {
    ///     fn guess(&mut self, _previous: &[Guess]) -> String {
    ///         "apple".to_string()
    ///     }
    /// }
    ///
    /// let mut guesser = SimpleGuesser;
    /// let guess = guesser.guess(&[]);
    /// assert_eq!(guess, "apple");
    /// ```
    fn guess(&mut self, previous: &[Guess]) -> String;
}

impl Guesser for fn(prev: &[Guess]) -> String {
    fn guess(&mut self, previous: &[Guess]) -> String {
        (*self)(previous)
    }
}

/// Represents the correctness of a guessed letter in the Wordle game.
///
/// This enum defines the possible states for a guessed letter:
/// - **`Correct`**: The letter is in the correct position.
/// - **`Misplaced`**: The letter is in the word but in the wrong position.
/// - **`Incorrect`**: The letter is not in the word.
///
/// These states are commonly represented by colored squares in Wordle:
/// - `Correct`: Green.
/// - `Misplaced`: Yellow.
/// - `Incorrect`: Gray.
///
/// # Example
/// ```
/// use wordle::game::Correctness;
///
/// let status = Correctness::Correct;
/// assert_eq!(status, Correctness::Correct);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub enum Correctness {
    /// The letter is in the word and in the correct position. Represented by a Green square.
    Correct,
    /// The letter is in the word but in the wrong position. Represented by a Yellow square.
    Misplaced,
    /// The letter is not in the word. Represented by a Gray square.
    Incorrect,
}

impl Correctness {
    /// Computes the correctness of a guess compared to the answer.
    ///
    /// This method evaluates the correctness of a guessed word by comparing it to the actual answer.
    /// The result is an array of `Correctness` values, where each value represents the relationship
    /// between the corresponding character in the guess and the answer:
    ///
    /// - **`Correct`**: The character matches the answer both in value and position.
    /// - **`Misplaced`**: The character exists in the answer but is in the wrong position.
    /// - **`Incorrect`**: The character does not appear in the answer.
    ///
    /// # Parameters
    /// - `answer`: The correct word to be guessed.
    /// - `guess`: The word guessed by the player.
    ///
    /// # Returns
    /// An array of `Correctness` values, one for each character in the guess.
    ///
    /// # Example
    /// ```
    /// use wordle::game::Correctness;
    ///
    /// assert_eq!(
    ///     Correctness::compute("apple", "apply"),
    ///     [
    ///         Correctness::Correct,
    ///         Correctness::Correct,
    ///         Correctness::Correct,
    ///         Correctness::Correct,
    ///         Correctness::Incorrect
    ///     ]
    /// );
    /// ```
    ///
    /// This method assumes that both `answer` and `guess` have the same length.
    /// Passing inputs with differing lengths may lead to undefined behavior.
    pub fn compute(answer: &str, guess: &str) -> [Self; 5] {
        assert_eq!(answer.len(), 5);
        assert_eq!(guess.len(), 5);

        let mut correctness = [Correctness::Incorrect; 5];

        // Mark correct
        for (i, (c_answer, c_guess)) in answer.chars().zip(guess.chars()).enumerate() {
            if c_answer == c_guess {
                correctness[i] = Correctness::Correct;
            }
        }

        // Mark misplaced
        let mut used = [false; 5];
        for (i, &c) in correctness.iter().enumerate() {
            if c == Correctness::Correct {
                used[i] = true;
            }
        }

        for (i, c_guess) in guess.chars().enumerate() {
            if correctness[i] == Correctness::Correct {
                continue;
            }

            if answer.chars().enumerate().any(|(i, c_answer)| {
                if c_answer == c_guess && !used[i] {
                    used[i] = true;
                    return true;
                }

                false
            }) {
                correctness[i] = Correctness::Misplaced;
            }
        }

        correctness
    }
}

#[cfg(test)]
mod test {
    mod play {
        use pretty_assertions::assert_eq;

        use crate::Wordle;

        macro_rules! guesser {
            (|$prev:ident| $impl:block) => {{
                struct G;

                impl $crate::game::Guesser for G {
                    fn guess(&mut self, $prev: &[$crate::game::Guess]) -> String {
                        $impl
                    }
                }
                G
            }};
        }

        #[test]
        fn first_attempt() {
            let game = Wordle::new();
            let guesser = guesser!(|_prev| { "apple".to_string() });
            assert_eq!(game.play("apple", guesser), Some(1));
        }

        #[test]
        fn two_guesses() {
            let game = Wordle::new();
            let guesser = guesser!(|prev| {
                if prev.len() == 1 {
                    return "right".to_string();
                }

                return "wrong".to_string();
            });

            assert_eq!(game.play("right", guesser), Some(2));
        }

        #[test]
        fn maximum_attempts() {
            let game = Wordle::new();
            let guesser = guesser!(|_prev| { "wrong".to_string() });

            assert_eq!(game.play("right", guesser), None);
        }

        #[test]
        fn word_not_in_dictionary() {
            let game = Wordle::new();
            let guesser = guesser!(|_prev| { "notaword".to_string() });

            let result = std::panic::catch_unwind(|| game.play("right", guesser));
            assert!(result.is_err());
        }
    }

    mod compute {
        use pretty_assertions::assert_eq;

        use crate::game::Correctness;

        macro_rules! correctness {
            (C) => {$crate::game::Correctness::Correct};
            (M) => {$crate::game::Correctness::Misplaced};
            (I) => {$crate::game::Correctness::Incorrect};
            ($($c:tt)+) => {[
                $(correctness!($c)),+
            ]}
        }

        #[test]
        fn all_correct() {
            assert_eq!(
                Correctness::compute("abcde", "abcde"),
                correctness![C C C C C]
            );
        }

        #[test]
        fn none_correct() {
            assert_eq!(
                Correctness::compute("abcde", "fghij"),
                correctness![I I I I I]
            )
        }

        #[test]
        fn all_misplaced() {
            assert_eq!(
                Correctness::compute("abcde", "edbca"),
                correctness![M M M M M]
            )
        }

        #[test]
        fn some_misplaced() {
            assert_eq!(
                Correctness::compute("abcde", "acbab"),
                correctness![C M M I I]
            )
        }

        #[test]
        fn repeated_misplaced() {
            assert_eq!(
                Correctness::compute("aabbc", "bbaac"),
                correctness![M M M M C]
            )
        }

        #[test]
        #[should_panic]
        fn compute_with_different_lengths() {
            Correctness::compute("apple", "apples");
        }
    }
}
