/// Extension trait for 2-tuples.
pub trait Tuple2Ext<A, B> {
    /// Maps over both elements of a 2-tuple.
    fn map_n<C, D, FA: FnOnce(&A) -> C, FB: FnOnce(&B) -> D>(&self, fa: FA, fb: FB) -> (C, D);
}

impl<A, B> Tuple2Ext<A, B> for (A, B) {
    fn map_n<C, D, FA: FnOnce(&A) -> C, FB: FnOnce(&B) -> D>(&self, fa: FA, fb: FB) -> (C, D) {
        (fa(&self.0), fb(&self.1))
    }
}

/// Extension trait for 3-tuples.
pub trait Tuple3Ext<A, B, C> {
    /// Maps over all elements of a 3-tuple.
    fn map_n<D, E, F, FA: FnOnce(&A) -> D, FB: FnOnce(&B) -> E, FC: FnOnce(&C) -> F>(
        &self,
        fa: FA,
        fb: FB,
        fc: FC,
    ) -> (D, E, F);
}

impl<A, B, C> Tuple3Ext<A, B, C> for (A, B, C) {
    fn map_n<D, E, F, FA: FnOnce(&A) -> D, FB: FnOnce(&B) -> E, FC: FnOnce(&C) -> F>(
        &self,
        fa: FA,
        fb: FB,
        fc: FC,
    ) -> (D, E, F) {
        (fa(&self.0), fb(&self.1), fc(&self.2))
    }
}

/// Extension trait for 4-tuples.
pub trait Tuple4Ext<A, B, C, D> {
    /// Maps over all elements of a 4-tuple.
    fn map_n<E, F, G, H, FA: FnOnce(&A) -> E, FB: FnOnce(&B) -> F, FC: FnOnce(&C) -> G, FD: FnOnce(&D) -> H>(
        &self,
        fa: FA,
        fb: FB,
        fc: FC,
        fd: FD,
    ) -> (E, F, G, H);
}

impl<A, B, C, D> Tuple4Ext<A, B, C, D> for (A, B, C, D) {
    fn map_n<E, F, G, H, FA: FnOnce(&A) -> E, FB: FnOnce(&B) -> F, FC: FnOnce(&C) -> G, FD: FnOnce(&D) -> H>(
        &self,
        fa: FA,
        fb: FB,
        fc: FC,
        fd: FD,
    ) -> (E, F, G, H) {
        (fa(&self.0), fb(&self.1), fc(&self.2), fd(&self.3))
    }
}

/// Extension trait for 5-tuples.
pub trait Tuple5Ext<A, B, C, D, E> {
    /// Maps over all elements of a 5-tuple.
    fn map_n<
        F,
        G,
        H,
        I,
        J,
        FA: FnOnce(&A) -> F,
        FB: FnOnce(&B) -> G,
        FC: FnOnce(&C) -> H,
        FD: FnOnce(&D) -> I,
        FE: FnOnce(&E) -> J,
    >(
        &self,
        fa: FA,
        fb: FB,
        fc: FC,
        fd: FD,
        fe: FE,
    ) -> (F, G, H, I, J);
}

impl<A, B, C, D, E> Tuple5Ext<A, B, C, D, E> for (A, B, C, D, E) {
    fn map_n<
        F,
        G,
        H,
        I,
        J,
        FA: FnOnce(&A) -> F,
        FB: FnOnce(&B) -> G,
        FC: FnOnce(&C) -> H,
        FD: FnOnce(&D) -> I,
        FE: FnOnce(&E) -> J,
    >(
        &self,
        fa: FA,
        fb: FB,
        fc: FC,
        fd: FD,
        fe: FE,
    ) -> (F, G, H, I, J) {
        (fa(&self.0), fb(&self.1), fc(&self.2), fd(&self.3), fe(&self.4))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tuple2_map_n() {
        let t = (1, "hello");
        let result = t.map_n(|a| a * 2, |b| b.len());
        assert_eq!(result, (2, 5));
    }

    #[test]
    fn tuple3_map_n() {
        let t = (1, 2.0, "hi");
        let result = t.map_n(|a| a + 1, |b| b * 2.0, |c| c.to_uppercase());
        assert_eq!(result, (2, 4.0, "HI".to_string()));
    }

    #[test]
    fn tuple4_map_n() {
        let t = (1, 2, 3, 4);
        let result = t.map_n(|a| a * 10, |b| b * 10, |c| c * 10, |d| d * 10);
        assert_eq!(result, (10, 20, 30, 40));
    }

    #[test]
    fn tuple5_map_n() {
        let t = (1, 2, 3, 4, 5);
        let result = t.map_n(|a| a + 1, |b| b + 1, |c| c + 1, |d| d + 1, |e| e + 1);
        assert_eq!(result, (2, 3, 4, 5, 6));
    }

    #[test]
    fn tuple2_map_n_type_change() {
        let t = (42, "world");
        let result = t.map_n(|a| a.to_string(), |b| b.len());
        assert_eq!(result, ("42".to_string(), 5));
    }
}
