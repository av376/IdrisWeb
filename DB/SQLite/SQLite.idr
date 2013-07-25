--Effect implementation of the SQLite3 Library.
-- Major credits go to SQLite3 library authors.
module IdrisWeb.DB.SQLite.SQLite
--import Sqlexpr
import Effects
import SQLiteCodes

%link C "sqlite3api.o"
%include C "sqlite3api.h"
%lib C "sqlite3"

%access public

-- Pointer to open database
data DBPointer = ValidConn Ptr
               | InvalidConn

-- Pointer to open prepared statement
data StmtPointer = ValidStmt Ptr
                 | InvalidStmt 


data DBError = DBConnFail
             | DBBindFail
             | DBStatementFail
             | DBExecuteFail
             | DBGetArgFail
             | DBFinaliseFail
             | DBCloseFail
             | DBResetFail

instance Show DBError where
  show DBConnFail = "Error connecting to database"
  show DBBindFail = "Error binding data to prepared statement"
  show DBStatementFail = "Error preparing statement"
  show DBExecuteFail = "Error executing prepared statement"
  show DBGetArgFail = "Error retrieving column information from the database"
  show DBCloseFail = "Error closing database connection"
  show DBFinaliseFail = "Error finalising prepared statement"
  show DBResetFail = "Error resetting row pointer"

-- Surely these can be consolidated into one?
-- Also, I should ideally fix the imports to stop duplicating these defs.
data DBVal = DBInt Int
           | DBText String
           | DBFloat Float
           | DBNull


-- Type synonym for a table
ResultSet : Type
ResultSet = List (List DBVal)

ArgPos : Type
ArgPos = Int


data Step = ConnectionOpened
          | PreparedStatementOpen
          | PreparedStatementBinding
          | PreparedStatementBound
          | PreparedStatementExecuting
--          | PreparedStatementResultsFetched



data SQLiteRes : Step -> Type where
  OpenConn : DBPointer -> SQLiteRes s
  OpenStmt : DBPointer -> StmtPointer -> SQLiteRes s
  ExecutingStmt : DBPointer -> StmtPointer -> StepResult -> SQLiteRes s

data Sqlite : Effect where
  -- Opens a connection to the database
  OpenDB : String -> Sqlite () (SQLiteRes ConnectionOpened) () 
  -- Closes the database handle
  CloseDB : Sqlite (SQLiteRes ConnectionOpened) () ()
  -- Creates a new prepared statement given a basic query string
  PrepareStatement : String -> Sqlite (SQLiteRes ConnectionOpened) 
                                      (SQLiteRes PreparedStatementOpen) ()

  -- Transition to the binding state, allowing for variables to be bound to the statement
  StartBind : Sqlite (SQLiteRes PreparedStatementOpen) (SQLiteRes PreparedStatementBinding) ()

  -- Binds an integer to the given argument
  BindInt : ArgPos -> Int -> Sqlite (SQLiteRes PreparedStatementBinding) 
                                    (SQLiteRes PreparedStatementBinding) ()

  -- Binds a float to the given argument
  BindFloat : ArgPos -> Float -> Sqlite (SQLiteRes PreparedStatementBinding) 
                                        (SQLiteRes PreparedStatementBinding) ()

  -- Binds a string to the given argument
  BindText : ArgPos -> (text : String) -> 
                       (length : Int) -> 
                       Sqlite (SQLiteRes PreparedStatementBinding) 
                              (SQLiteRes PreparedStatementBinding) ()

  -- Binds a NULL value to the given argument
  BindNull : ArgPos -> Sqlite (SQLiteRes PreparedStatementBinding) 
                              (SQLiteRes PreparedStatementBinding) ()

  -- Transitions out of the binding state, allowing for the query to be executed
  FinishBind : Sqlite (SQLiteRes PreparedStatementBinding) (SQLiteRes PreparedStatementBound) ()

  -- Executes the given prepared statement
  ExecuteStatement : Sqlite (SQLiteRes PreparedStatementBound) (SQLiteRes PreparedStatementExecuting) ()

  -- Fetches the results of the previously-executed query
  {-FetchResults : Sqlite (SQLiteRes PreparedStatementExecuting) 
                        (SQLiteRes PreparedStatementResultsFetched) 
                        Table
                        -}
  -- Disposes of a prepared statement
  Finalise : Sqlite (SQLiteRes PreparedStatementExecuting) (SQLiteRes ConnectionOpened) ()


  ----- Operations on result sets.
  -- SQLite returns data on a row-by-row basis, which is advanced using the step
  -- function. The position of this pointer can also be reset using the reset function.

  -- These operations are done performed on the current row.
  -- Given a column index, gets the name of the column
  GetColumnName : Int -> Sqlite (SQLiteRes PreparedStatementExecuting) 
                                (SQLiteRes PreparedStatementExecuting)
                                String


  -- Given a column index, returns the size in bytes
  GetColumnDataSize : Int -> Sqlite (SQLiteRes PreparedStatementExecuting)
                                    (SQLiteRes PreparedStatementExecuting)
                                    Int


  -- Not sure how we should handle blobs. Underlying library says string, but I don't
  -- think this entirely makes sense. Will come back to it, omitting for now.

  -- Given a column index, returns the data as an Idris string.
  GetColumnText : Int -> Sqlite (SQLiteRes PreparedStatementExecuting)
                                (SQLiteRes PreparedStatementExecuting)
                                String

  -- Given a column index, returns the data as an Idris integer.
  GetColumnInt : Int -> Sqlite (SQLiteRes PreparedStatementExecuting)
                               (SQLiteRes PreparedStatementExecuting)
                               Int

  -- Advance the row pointer
  -- TODO: We will get a particular status code when we reach the end of the
  --       results. Ideally, this should be encoded as a state to ensure that
  --       step is not called once all rows have been seen.
  RowStep : Sqlite (SQLiteRes PreparedStatementExecuting)
                   (SQLiteRes PreparedStatementExecuting)
                   StepResult

  Reset : Sqlite (SQLiteRes PreparedStatementExecuting)
                 (SQLiteRes PreparedStatementExecuting)
                 ()



-- TODO: Must also do this in IOExcept, runtime errors are bad, mmkay
instance Handler Sqlite (IOExcept DBError) where
  handle () (OpenDB file) k = do
    ff <- ioe_lift (mkForeign (FFun "sqlite3_open_idr" [FString] FPtr) file)
    is_null <- ioe_lift (nullPtr ff)
    -- We still have to transition to ConnectionOpened, even if the
    -- open operation failed. We can, however, tag the connection resource
    -- as invalid, and pattern match on it so that no further effects occur.
    if (not is_null) then k (OpenConn (ValidConn ff)) ()
                     else ioe_fail DBConnFail -- k (OpenConn InvalidConn) False
    -- k (Valid ff) ()

  -- TODO: Probably best to do some error handling here
  handle (OpenConn (ValidConn conn) ) CloseDB k = do
    res <- io_lift (mkForeign (FFun "sqlite3_close_idr" [FPtr] FInt) conn)
    -- Underlying library returns 0 on success, some error code otherwise
    if res == 0 then k () ()
                else ioe_fail DBCloseFail

  -- If the handle is invalid, just return true without doing anything
  handle (OpenConn (InvalidConn)) CloseDB k = k () ()

  -- Compile a prepared statement.
  -- If there's no connection, do nothing and return false, with an invalid statement
  handle (OpenConn (InvalidConn)) (PrepareStatement s) k = k (OpenStmt InvalidConn InvalidStmt) False

  -- Otherwise, try to create a prepared statement
  handle (OpenConn (ValidConn c)) (PrepareStatement s) k = do
    ps_ptr <- ioe_lift (mkForeign (FFun "sqlite3_prepare_idr" [FPtr, FString] FPtr) c s)
    is_null <- ioe_lift (nullPtr ps_ptr)
    if (not is_null) then k (OpenStmt (ValidConn c) (ValidStmt ps_ptr)) ()
                     else ioe_fail DBStatementFail
        --k (OpenStmt (ValidConn c) (InvalidStmt)) False

  -- Bind state transition functions
  handle (OpenStmt (ValidConn c) (ValidStmt s)) StartBind k = do
    k (OpenStmt (ValidConn c) (ValidStmt s)) ()

  handle (OpenStmt (ValidConn c) InvalidStmt) StartBind k = do
    k (OpenStmt (ValidConn c) InvalidStmt) ()

  handle (OpenStmt InvalidConn x) StartBind k = k (OpenStmt InvalidConn x) ()

  handle (OpenStmt (ValidConn c) (ValidStmt s)) FinishBind k = do
    k (OpenStmt (ValidConn c) (ValidStmt s)) ()

  handle (OpenStmt (ValidConn c) InvalidStmt) FinishBind k = do
    k (OpenStmt (ValidConn c) InvalidStmt) ()

  handle (OpenStmt InvalidConn x) FinishBind k = k (OpenStmt InvalidConn x) ()


  -- Bind functions
  handle (OpenStmt (ValidConn c) (ValidStmt s)) (BindInt pos i) k = do
    res <- ioe_lift (mkForeign (FFun "sqlite3_bind_int_idr" [FPtr, FInt, FInt] FPtr) c pos i)
    is_null <- ioe_lift (nullPtr res)
    if (not is_null) then k (OpenStmt (ValidConn c) (ValidStmt s)) ()
                     else ioe_fail DBBindFail

  handle (OpenStmt (ValidConn c) (ValidStmt s)) (BindFloat pos f) k = do
    res <- ioe_lift (mkForeign (FFun "sqlite3_bind_float_idr" [FPtr, FInt, FFloat] FPtr) c pos f)
    is_null <- nullPtr res
    if (not is_null) then k (OpenStmt (ValidConn c) (ValidStmt s)) ()
                     else ioe_fail DBBindFail


  handle (OpenStmt (ValidConn c) (ValidStmt s)) (BindText pos str len) k = do
    res <- ioe_lift (mkForeign (FFun "sqlite3_bind_text_idr" [FPtr, FString, FInt, FInt] FPtr) c str pos len)
    is_null <- ioe_lift (nullPtr res)
    if (not is_null) then k (OpenStmt (ValidConn c) (ValidStmt s)) ()
                     else ioe_fail DBBindFail 

  handle (OpenStmt (ValidConn c) (ValidStmt s)) (BindNull pos) k = do
    res <- ioe_lift (mkForeign (FFun "sqlite3_bind_null_idr" [FPtr, FInt] FPtr) c pos)
    is_null <- ioe_lift (nullPtr res)
    if (not is_null) then k (OpenStmt (ValidConn c) (ValidStmt s)) ()
                     else ioe_fail DBBindFail

 
  -- Row operations
  -- These only pass the calls to the underlying library if the ExecutingStmt
  -- is tagged with StepComplete. This means that the resource access protocol
  -- is adhered to.

  -- Unfortunately, we can't guarantee that conversions are correctly made, since
  -- failure is not indicated by the underlying SQLite3 library. Trying to get a
  -- Int from a String field, for example, will either convert a string representation
  -- of the integer to an Int, or return the default value 0.
  handle (ExecutingStmt (ValidConn c) (ValidStmt s) StepComplete) (GetColumnName i) k = do
    res <- ioe_lift (mkForeign (FFun "sqlite3_column_name_idr" [FPtr, FInt] FString) c i)
    k (ExecutingStmt (ValidConn c) (ValidStmt s) StepComplete) res

  handle (ExecutingStmt (ValidConn c) (ValidStmt s) StepComplete) (GetColumnDataSize i) k = do
    res <- ioe_lift (mkForeign (FFun "sqlite3_column_bytes_idr" [FPtr, FInt] FInt) c i)
    k (ExecutingStmt (ValidConn c) (ValidStmt s) StepComplete) res

  handle (ExecutingStmt (ValidConn c) (ValidStmt s) StepComplete) (GetColumnInt i) k = do
    res <- ioe_lift (mkForeign (FFun "sqlite3_column_int_idr" [FPtr, FInt] FInt) c i)
    k (ExecutingStmt (ValidConn c) (ValidStmt s) StepComplete) res

  -- Failure is, however, indicated in the getColumnText function. This allows us to fail the
  -- computation, should a null pointer be returned. This is necessary, as null pointers will
  -- cause a segmentation fault.
  handle (ExecutingStmt (ValidConn c) (ValidStmt s) StepComplete) (GetColumnText i) k = do
    res <- ioe_lift (mkForeign (FFun "sqlite3_column_text_idr" [FPtr, FInt] FPtr) c i)
    is_null <- ioe_lift (nullPtr res)
    if (not is_null) then do res' <- ioe_lift (mkForeign (FFun "sqlite3_column_text_idr" [FPtr, FInt] FString) c i)
                             k (ExecutingStmt (ValidConn c) (ValidStmt s) StepComplete) res'
                     else ioe_fail DBArgFail


  -- Pass-through handlers
  -- If these get executed, then we're attempting to get row info when there's no valid row
  -- loaded in by nextRow (for example if we have retrieved all valid rows, or some failure has
  -- occurred along the way). Generally, this behaviour in the C library is undefined. We may,
  -- however, use our knowledge of this to catch this condition, throw an exception and in
  -- turn prevent these calls to the underlying library from being made.
  handle (ExecutingStmt x y z) (GetColumnName i) k = ioe_fail DBArgFail

  handle (ExecutingStmt x y z) (GetColumnDataSize i) k = ioe_fail DBArgFail 

  handle (ExecutingStmt x y z) (GetColumnText i) k = ioe_fail DBArgFail 

  handle (ExecutingStmt x y z) (GetColumnInt i) k = ioe_fail DBArgFail 

  -- Step and reset
  -- Only actually call the underlying library if in either the Unstarted / StepComplete
  -- states. Calling this in other states should fail without calling the library.
  handle (ExecutingStmt (ValidConn c) (ValidStmt s) Unstarted) RowStep k = do
    res <- ioe_lift (mkForeign (FFun "sqlite3_step_idr" [FPtr] FInt) c)
    let step_res = stepResult res
    -- If we get a StepFail, then something's gone wrong in the underlying library.
    -- We detect this, and report it as an exception. Other conditions, for example
    -- NoMoreRows (if all rows have been evaluated) are instead reflected in the resource.
    case step_res of 
      StepFail => ioe_fail DBExecuteFail
      _ => k (ExecutingStmt (ValidConn c) (ValidStmt s) step_res) step_res

  handle (ExecutingStmt (ValidConn c) (ValidStmt s) StepComplete) RowStep k = do
    res <- ioe_lift (mkForeign (FFun "sqlite3_step_idr" [FPtr] FInt) c)
    let step_res = stepResult res
    case step_res of
      StepFail => ioe_fail DBExecuteFail
      _ => k (ExecutingStmt (ValidConn c) (ValidStmt s) step_res) step_res

  -- RowStep shouldn't be called unless we are in the Unstarted / StepComplete row states.
  -- If this is called in any other state, it's an exception.
  handle (ExecutingStmt x y z) RowStep k = 
    ioe_fail DBExecuteFail

  handle (ExecutingStmt (ValidConn c) (ValidStmt s) x) Reset k = do
    res <- ioe_lift (mkForeign (FFun "sqlite3_reset_idr" [FPtr] FInt) c)
    if res == sqlite_OK then
       k (ExecutingStmt (ValidConn c) (ValidStmt s) Unstarted) ()
     else
       ioe_fail DBResetFail

  handle (ExecutingStmt (ValidConn c) InvalidStmt x) Reset k = 
    ioe_fail DBResetFail 
  handle (ExecutingStmt InvalidConn x y) Reset k = 
    ioe_fail DBResetFail

  -- Finalise statement
  handle (ExecutingStmt (ValidConn c) (ValidStmt s) x) Finalise k = do
    res <- ioe_lift (mkForeign (FFun "sqlite3_finalize_idr" [FPtr] FInt) s)
    if res == sqlite_OK then k (OpenConn (ValidConn c)) ()
                        else ioe_fail DBFinaliseFail

  handle (ExecutingStmt (ValidConn c) InvalidStmt x) Finalise k = 
    ioe_fail DBFinaliseFail

  handle (ExecutingStmt InvalidConn x y) Finalise k = 
   ioe_fail DBFinaliseFail
 
SQLITE : Type -> EFFECT
SQLITE t = MkEff t Sqlite

-- Effect functions
openDB : String -> EffM (IOExcept DBError) [SQLITE ()] [SQLITE (SQLiteRes ConnectionOpened)] Bool
openDB filename = (OpenDB filename)

closeDB : EffM (IOExcept DBError) [SQLITE (SQLiteRes ConnectionOpened)] [SQLITE ()] Bool
closeDB = CloseDB 

prepareStatement : String -> EffM (IOExcept DBError) [SQLITE (SQLiteRes ConnectionOpened)] 
                                    [SQLITE (SQLiteRes PreparedStatementOpen)] Bool
prepareStatement stmt = (PrepareStatement stmt)

startBind : EffM (IOExcept DBError) [SQLITE (SQLiteRes PreparedStatementOpen)] 
                   [SQLITE (SQLiteRes PreparedStatementBinding)] ()
startBind = StartBind

bindInt : ArgPos -> Int -> Eff (IOExcept DBError) [SQLITE (SQLiteRes PreparedStatementBinding)] Bool
bindInt pos i = (BindInt pos i)

bindFloat : ArgPos -> Float -> Eff (IOExcept DBError) [SQLITE (SQLiteRes PreparedStatementBinding)] Bool
bindFloat pos i = (BindFloat pos i)

natToInt : Nat -> Int
natToInt O = 0
natToInt (S k) = 1 + (natToInt k)

bindText : ArgPos -> String -> Eff (IOExcept DBError) [SQLITE (SQLiteRes PreparedStatementBinding)] Bool
bindText pos str = (BindText pos str str_len)
  where 
        str_len : Int
        str_len = natToInt (length str)

bindNull : ArgPos -> Eff (IOExcept DBError) [SQLITE (SQLiteRes PreparedStatementBinding)] Bool
bindNull pos = (BindNull pos)

finishBind : EffM (IOExcept DBError) [SQLITE (SQLiteRes PreparedStatementBinding)] 
                    [SQLITE (SQLiteRes PreparedStatementBound)] Bool
finishBind = FinishBind

beginExecution : EffM (IOExcept DBError) [SQLITE (SQLiteRes PreparedStatementBound)] 
                        [SQLITE (SQLiteRes PreparedStatementExecuting)] ()
beginExecution = ExecuteStatement

finaliseStatement : EffM (IOExcept DBError) [SQLITE (SQLiteRes PreparedStatementExecuting)]
                           [SQLITE (SQLiteRes ConnectionOpened)]
                           Bool
finaliseStatement = Finalise

getColumnName : Int -> Eff (IOExcept DBError) [SQLITE (SQLiteRes PreparedStatementExecuting)] String
getColumnName pos = (GetColumnName pos)

getColumnDataSize : Int -> Eff (IOExcept DBError) [SQLITE (SQLiteRes PreparedStatementExecuting)] Int
getColumnDataSize pos = (GetColumnDataSize pos)

getColumnText : Int -> Eff (IOExcept DBError) [SQLITE (SQLiteRes PreparedStatementExecuting)] String
getColumnText pos = (GetColumnText pos)

getColumnInt : Int -> Eff (IOExcept DBError) [SQLITE (SQLiteRes PreparedStatementExecuting)] Int
getColumnInt pos = (GetColumnInt pos)

nextRow : Eff (IOExcept DBError) [SQLITE (SQLiteRes PreparedStatementExecuting)] StepResult
nextRow = RowStep
resetPos : Eff (IOExcept DBError) [SQLITE (SQLiteRes PreparedStatementExecuting)] Bool
resetPos = Reset

{-
-- Utility functions to help handle failure
-- TODO: These errors should ideally be encoded as ADTs
connFail : EffM (IOExcept DBError) [SQLITE (SQLiteRes ConnectionOpened)] [SQLITE ()] String
connFail = do closeDB
              pure "Error connecting to database."

stmtFail : EffM (IOExcept DBError) [SQLITE (SQLiteRes PreparedStatementOpen)] [SQLITE ()] String
stmtFail = do
  -- These will all fall through without having any effect.
  -- Right Way To Do It?
  startBind
  finishBind
  beginExecution
  finaliseStatement
  closeDB -- Close the connection
  pure "Error preparing statement"

bindFail : EffM (IOExcept DBError) [SQLITE (SQLiteRes PreparedStatementBound)] [SQLITE ()] String
bindFail = do
  beginExecution
  finaliseStatement
  closeDB
  pure "Error binding to statement"

executeFail : EffM (IOExcept DBError) [SQLITE (SQLiteRes PreparedStatementExecuting)] [SQLITE ()] String
executeFail = do
  finaliseStatement
  closeDB
  pure "Error executing statement"


executeInsert' : EffM (IOExcept DBError) [SQLITE (SQLiteRes PreparedStatementExecuting)] [SQLITE (SQLiteRes ConnectionOpened)] (Either String Int) -- (Maybe Int)
executeInsert' = do
 id_res <- nextRow 
 case id_res of
   StepComplete => do
     last_insert_id <- getColumnInt 0
     finaliseStatement
     Effects.pure $ Right last_insert_id
   NoMoreRows => do finaliseStatement
                    Effects.pure $ Left "Error getting insert ID! NoMoreRows"
   StepFail => do finaliseStatement
                  Effects.pure $ Left "Error getting insert ID! StepFail"

-- Execute an insert statement, get the last inserted row ID
-- TODO: Create a binding to the SQLITE API function, instead of getting
--       last row ID by a query
executeInsert : EffM (IOExcept DBError) [SQLITE (SQLiteRes PreparedStatementExecuting)] [SQLITE (SQLiteRes ConnectionOpened)] (Either String Int)
executeInsert = do
  next_row_res <- nextRow
  case next_row_res of
-- Error with executing insert statement
    StepFail => do
      finaliseStatement
      Effects.pure $ Left "Error inserting! next_row_res executeFail"
    _ => do
      finaliseStatement
      let insert_id_sql = "SELECT last_insert_rowid();"
      sql_prep_res <- prepareStatement insert_id_sql
      if sql_prep_res then do
        startBind
        finishBind
        beginExecution 
        executeInsert'
      else do
        startBind
        finishBind
        beginExecution
        finaliseStatement
        Effects.pure $ Left "Error inserting! StmtFail"

multiBind' : List (Int, DBVal) -> Eff (IOExcept DBError) [SQLITE (SQLiteRes PreparedStatementBinding)] ()
multiBind' [] = Effects.pure ()
multiBind' ((pos, (DBInt i)) :: xs) = do bindInt pos i
                                         multiBind' xs
multiBind' ((pos, (DBFloat f)) :: xs) = do bindFloat pos f
                                           multiBind' xs
multiBind' ((pos, (DBText t)) :: xs) = do bindText pos t
                                          multiBind' xs
-- Binds multiple values within a query
multiBind : List (Int, DBVal) -> EffM (IOExcept DBError) [SQLITE (SQLiteRes PreparedStatementOpen)] [SQLITE (SQLiteRes PreparedStatementBound)] Bool
multiBind vals = do
  startBind
  multiBind' vals
  finishBind

-- Convenience function to abstract around some of the boilerplate code.
-- Takes in the DB name, query, a list of (position, variable value) tuples,
-- a function to process the returned data, 
executeSelect : String ->
                String -> 
                List (Int, DBVal) -> 
                (Eff (IOExcept DBError) [SQLITE (SQLiteRes PreparedStatementExecuting)] (Either String ResultSet)) -> 
                Eff (IOExcept DBError) [SQLITE ()] (Either String ResultSet)
executeSelect db_name q bind_vals fn = 
catch ( do
  openDB db_name
  prepareStatement q
  multiBind bind_vals
  beginExecution
  res <- fn
  finaliseStatement
  closeDB ) (\err => Left err)
{-
        Effects.pure $ res
      else do
        err <- bindFail
        Effects.pure $ Left err
    else do
      err <- stmtFail
      Effects.pure $ Left err
  else do
    err <- connFail
    Effects.pure $ Left err
  -}    
