from io import StringIO
from sexpdata import dump

class VerificationError(Exception):
    def __init__(self, message):
        self.message = message
        Exception.__init__(self, message)

class AlreadyDefinedError(VerificationError):
    def __init__(self, name):
        VerificationError.__init__(self, "“%s” is already defined" % name)

class InvalidTermError(VerificationError):
    def __init__(self, expr):
        stream = StringIO()
        dump(expr, stream)
        VerificationError.__init__(
            self, "invalid term: %s" % stream.getvalue()
        )

class UnificationError(VerificationError):
    def __init__(self, α, β):
        VerificationError.__init__(
            self,
            "“%s” cannot be unified with “%s”" % (α, β)
        )

class AdmittedError(VerificationError):
    def __init__(self):
        VerificationError.__init__(self, "admitted")

class NotDefinedError(VerificationError):
    def __init__(self, name):
        VerificationError.__init__(self, "“%s” is not defined" % name)