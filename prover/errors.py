class VerificationError(Exception):
    def __init__(self, message):
        self.message = message
        Exception.__init__(self, message)

class UnificationError(VerificationError):
    def __init__(self, α, β):
        VerificationError.__init__(
            self,
            "“%s” cannot be unified with “%s”" % (α, β)
        )

class ModusPonensError(VerificationError):
    def __init__(self, φ):
        VerificationError.__init__(
            self,
            "“%s” does not have modus ponens rule" % φ
        )

class AdmittedError(VerificationError):
    def __init__(self):
        VerificationError.__init__(self, "admitted")

class NotDefinedError(VerificationError):
    def __init__(self, name):
        VerificationError.__init__(self, "“%s” is not defined" % name)