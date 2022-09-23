/*
 * Copyright (c) 2018 Frank Fischer <frank-fischer@shadow-soft.de>
 *
 * This program is free software: you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see  <http://www.gnu.org/licenses/>
 */

use std::collections::VecDeque;

pub trait ItemQueue<I> {
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn len(&self) -> usize;

    fn clear(&mut self);

    fn push(&mut self, u: I);

    fn pop(&mut self) -> Option<I>;
}

impl<'a, I, D> ItemQueue<I> for &'a mut D
where
    D: ItemQueue<I>,
{
    fn is_empty(&self) -> bool {
        (**self).is_empty()
    }

    fn len(&self) -> usize {
        (**self).len()
    }

    fn clear(&mut self) {
        (**self).clear()
    }

    fn push(&mut self, u: I) {
        (**self).push(u)
    }

    fn pop(&mut self) -> Option<I> {
        (**self).pop()
    }
}

impl<I> ItemQueue<I> for VecDeque<I> {
    fn is_empty(&self) -> bool {
        VecDeque::is_empty(self)
    }

    fn len(&self) -> usize {
        VecDeque::len(self)
    }

    fn clear(&mut self) {
        VecDeque::clear(self)
    }

    fn push(&mut self, u: I) {
        VecDeque::push_back(self, u)
    }

    fn pop(&mut self) -> Option<I> {
        VecDeque::pop_front(self)
    }
}
