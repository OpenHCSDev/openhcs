{
  "stages": [
    {
      "recipes": [
        {
          "recipe_id": "stage-1-insert_before_target",
          "operations": [
            {
              "operation": "insert_before_target",
              "file_path": "openhcs/runtime/napari_viewer_server.py",
              "target_qualname": "NapariNavigationControlMessageAction",
              "rationale": "Declare the one owner of native Napari navigation calculations.",
              "source": "class NapariViewerNavigationAuthority:\n    \"\"\"Own route-local navigation calculations shared by UI and transport actions.\"\"\""
            }
          ],
          "architecture_guards": [],
          "reason": "",
          "authority_claims": []
        }
      ],
      "architecture_guards": []
    },
    {
      "recipes": [
        {
          "recipe_id": "stage-2-add_class_base",
          "operations": [
            {
              "operation": "add_class_base",
              "file_path": "openhcs/runtime/napari_viewer_server.py",
              "target_qualname": "NapariNavigationControlMessageAction",
              "rationale": "Derive the navigation control action from the shared navigation authority.",
              "base_name": "NapariViewerNavigationAuthority"
            }
          ],
          "architecture_guards": [],
          "reason": "",
          "authority_claims": []
        }
      ],
      "architecture_guards": []
    },
    {
      "recipes": [
        {
          "recipe_id": "stage-3-promote_class_members_to_ancestor",
          "operations": [
            {
              "operation": "promote_class_members_to_ancestor",
              "file_path": "openhcs/runtime/napari_viewer_server.py",
              "target_qualname": "NapariNavigationControlMessageAction",
              "rationale": "Move the shared navigation implementation to its declared owner without copying method bodies.",
              "destination": {
                "target_id": null,
                "file_path": "openhcs/runtime/napari_viewer_server.py",
                "target_qualname": "NapariViewerNavigationAuthority"
              },
              "member_names": [
                "result_element_axis_indices",
                "axis_step",
                "_axis_position",
                "_validate_local_axis_index"
              ]
            }
          ],
          "architecture_guards": [],
          "reason": "",
          "authority_claims": []
        }
      ],
      "architecture_guards": []
    },
    {
      "recipes": [
        {
          "recipe_id": "stage-4-patch_target",
          "operations": [
            {
              "operation": "patch_target",
              "replacements": [
                {
                  "old_source": "navigation = NapariNavigationControlMessageAction()",
                  "new_source": "navigation = NapariViewerNavigationAuthority()"
                }
              ],
              "file_path": "openhcs/runtime/napari_viewer_server.py",
              "target_qualname": "NapariResultSelectionController._apply_selection",
              "rationale": "Make native ROI selection consume the shared navigation authority rather than the transport action leaf."
            }
          ],
          "architecture_guards": [],
          "reason": "",
          "authority_claims": []
        }
      ],
      "architecture_guards": []
    }
  ]
}
