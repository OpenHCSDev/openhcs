"""One OpenHCS session: datasets, pipelines, compile, run and their events.

The Qt GUI, headless MCP and any other client render :class:`SessionView`
states and call :meth:`Session.invoke` with :class:`SessionOperation` classes.
No client holds session state of its own.
"""
