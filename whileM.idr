whileM' : (Monad m, Monad f, Alternative f) => (a -> Bool) -> m a -> m (f a)
whileM' p f = go
    where go = do
            x <- f
            if p x
                then do
                        xs <- go
                        pure (pure x <|> xs)
                else pure empty

whileM : Monad m => (a -> Bool) -> m a -> m (List a)
whileM = whileM'