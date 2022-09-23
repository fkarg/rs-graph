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

pub trait ItemStack<I> {
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn len(&self) -> usize;

    fn clear(&mut self);

    fn push(&mut self, u: I);

    fn pop(&mut self) -> Option<I>;

    fn top(&self) -> Option<&I>;

    fn top_mut(&mut self) -> Option<&mut I>;
}

impl<'a, I, D> ItemStack<I> for &'a mut D
where
    D: ItemStack<I>,
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

    fn top(&self) -> Option<&I> {
        (**self).top()
    }

    fn top_mut(&mut self) -> Option<&mut I> {
        (**self).top_mut()
    }
}

impl<I> ItemStack<I> for Vec<I> {
    fn is_empty(&self) -> bool {
        Vec::is_empty(self)
    }

    fn len(&self) -> usize {
        Vec::len(self)
    }

    fn clear(&mut self) {
        Vec::clear(self)
    }

    fn push(&mut self, u: I) {
        Vec::push(self, u)
    }

    fn pop(&mut self) -> Option<I> {
        Vec::pop(self)
    }

    fn top(&self) -> Option<&I> {
        self.as_slice().last()
    }

    fn top_mut(&mut self) -> Option<&mut I> {
        self.as_mut_slice().last_mut()
    }
}
