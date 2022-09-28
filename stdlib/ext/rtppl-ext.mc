
-- Representation of a file descriptor.
type FileDescriptor = Int

-- A time-stamped value is represented as a sequence of floating-point values.
type TimeStampedValue = [Float]

-- Functions for interacting with other processes.
external openFd : String -> FileDescriptor
external readFd : FileDescriptor -> Int -> TimeStampedValue
external writeFd : FileDescriptor -> TimeStampedValue -> ()
